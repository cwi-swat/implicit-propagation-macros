package nl.cwi.implicitpropagation.macros

import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.reflect.ClassTag

object Wire{
  object StackHolder{
    var stacks: scala.collection.mutable.Map[Class[_], scala.collection.mutable.Stack[AnyRef]]  = 
	              scala.collection.mutable.Map[Class[_], scala.collection.mutable.Stack[AnyRef]]  ()
  }
   
  def wireAlg[F,G,Alg[_],AAlg](actualAlg: Alg[_]): Alg[G] = 
    macro wireAlgImpl[F,G,Alg, AAlg]
  
  def wireAlgImpl[F: c.WeakTypeTag, G: c.WeakTypeTag, Alg[_], AAlg: c.WeakTypeTag]
    (c:Context)(
//        f: c.Expr[Class[F]],
//        g: c.Expr[Class[G]], 
//        alg: c.Expr[Class[AAlg]],
        actualAlg: c.Expr[Alg[_]]): c.Expr[Alg[G]] ={
     import c.universe._
     val fType = //implicitly[c.WeakTypeTag[F]].tpe
             weakTypeTag[F].tpe
     val gType = implicitly[c.WeakTypeTag[G]].tpe
     val algType = implicitly[c.WeakTypeTag[AAlg]].tpe
     val returnType = implicitly[c.WeakTypeTag[AAlg]].tpe
     val concreteType = actualAlg.actualType
     println(algType)
     println(algType.typeSymbol.fullName)
     val newName = c.freshName()
     val r = c.Expr[AAlg](c.parse(s"{val ${newName} = new ${algType.typeConstructor}[${gType}]{ }; ${newName}}"))
     // How to add the methods now to this already constructed object?
     
     val m = c.mirror
     val proxiedObjName = c.freshName()  
     val methods = returnType.members.filter(m => m.isMethod && m.isAbstract)
       .map(m => m.asMethod).map(m => toAlgMethodDef(c)(m, fType, gType, proxiedObjName)) mkString "\n"
      
     println(returnType)
     println(methods)
     val sourceCode = 
       s"""{
             val ${proxiedObjName} = new ${concreteType.typeConstructor}{};
             val ${newName} = new ${algType.typeConstructor}[${gType}]{
                ${methods}
             }; 
             ${newName}}""";
     println("generated:")
     println("----------")
     println(sourceCode)        
      c.Expr[Alg[G]](c.parse(sourceCode))
  }
  
  // it means that the newParams (of the lifted operation) contains the ones of the proxied operation
  def subsumesSignature(c:Context)(originalParams: List[c.universe.Symbol], newParams: List[c.universe.Symbol]): Boolean = {
    true
  }
  
  def toOperationMethodDef(c:Context)
    (m: c.universe.MethodSymbol,
     originalParams: List[c.universe.Symbol],
     newParams: List[c.universe.Symbol],
     wrappedObjName: String): String ={
    val parametersSignature =
        newParams.map(
           m => s"${m.name} : ${m.typeSignature.normalize}") mkString ", "
    val parsToRemember = newParams
          .filter(p => originalParams.exists(p.typeSignature.normalize <:< _.typeSignature.normalize) 
                   || originalParams.size == 0) // the latter condition to account for the parameterless case
        
    val body = 
      //if (subsumesSignature(c)(originalParams, newParams)){
      if (!parsToRemember.isEmpty){
        val args =
          originalParams.map(
             m => m.name) mkString ", "
           
        val actualInvocation = s"${wrappedObjName}.${m.name}(${args})"
    
        val pushingCode = 
          parsToRemember.map(p => s"stacks.getOrElseUpdate(classOf[${p.typeSignature.normalize}], new scala.collection.mutable.Stack[AnyRef]).push(${p.name})") mkString "\n"
        val poppingCode = 
          parsToRemember.map(p => s"stacks.get(classOf[${p.typeSignature.normalize}]).get.pop()") mkString "\n"
        s"""
               ${pushingCode}
	             try{
	               ${actualInvocation}
	             }
	             finally{
	               ${poppingCode}
	             }        
        """
      }
      else{
        // result.eval(stacks(classOf[Env]).top.asInstanceOf[Env])
        val args =
          originalParams.map(
             p => s"stacks(classOf[${p.typeSignature.normalize}]).top.asInstanceOf[${p.typeSignature.normalize}]") mkString ", "
        s"${wrappedObjName}.${m.name}(${args})"
      }
     
     s"""def ${m.name}(${parametersSignature}): ${m.returnType} = {
           ${body}
    }"""
  }
  
   
  def toOperationMethodDefs(c:Context)(wrappedOperationMethod: Option[c.universe.Symbol],
      m: c.universe.MethodSymbol, wrappedObjName: String)
    = 
    // Assuming overloaded methods that execute the attemtped 
    // semantics of the "operation".
     wrappedOperationMethod match{
      case Some(woMethod) =>{
        val woPLists = woMethod.asMethod.paramLists
        println(m.name)
        if (woPLists.size == 1){
            m.paramLists.map(pList => toOperationMethodDef(c)(m, woPLists.head, pList, wrappedObjName)) mkString "\n"
        }else // This exception is also triggered in the case of parameterless scala methods (no parentheses)
          throw new Exception("Operation cannot have overloaded methods.")
          
      }
      case None => throw new Exception("Not implementation found for this abstract member: "+m.name)
     }
  
  // It'd be possible also to carry to this point all the other operations, e.g.,
  // IEvalStorage + IEvalBinding, in the case of lifiting IEvalArith
  // In that sense, maybe the operations would be clearer
  def buildOperation(c:Context)(wrappedOperation: c.universe.Type, newOperation: c.universe.Type, wrappedObjName: String): String = {
    // The common case is that there is just one method, because one can think
    // of operations as functions implementing certain functionality
    val methods = newOperation.members.filter(m => m.isMethod && m.isAbstract)
       .map(_.asMethod)
       .map(m => toOperationMethodDefs(c)(wrappedOperation.members.filter(m => m.isMethod && m.isAbstract).find(_.asMethod.name.decoded == m.name.decoded), m, wrappedObjName)) mkString "\n"
      
    s"""new ${newOperation}{
        import nl.cwi.implicitpropagation.macros.Wire.StackHolder._
        ${methods}     
    }"""
  }
  
  
  def toAlgMethodDef(c:Context)(m: c.universe.MethodSymbol, wrappedOperation: c.universe.Type, newOperation: c.universe.Type, proxiedObjName: String)
    = {
      val parametersSignature =
        m.paramLists.head.map(
           m => s"${m.name} : ${ if (m.typeSignature.typeSymbol.asType.isAbstractType) newOperation else m.typeSignature}") mkString ", "
      val args =
        m.paramLists.head.map(
           m => m.name) mkString ", "
           
           
      val resultName = c.freshName()
      s"""def ${m.name}(${parametersSignature}): ${newOperation} = {
             val ${resultName} = ${proxiedObjName}.${m.name}(${args})
             ${buildOperation(c)(wrappedOperation, newOperation, resultName)}
      }"""
    }
    
  
  def wireAlg1[JustAlg, Alg[_]](
      alg: Alg[_]): Alg[String]
      = macro wireAlgImpl1[JustAlg, Alg]
  
  
  def wireAlgImpl1[JustAlg: c.WeakTypeTag, Alg[_]]
    (c:Context)(
       alg: c.Expr[Alg[_]]): c.Expr[Alg[String]] 
    ={
     import c.universe._
     val algType = implicitly[c.WeakTypeTag[Alg[_]]].tpe
     val newName = c.freshName()
     c.Expr[Alg[String]](c.parse(s"{val ${newName} = new ${algType.typeSymbol.fullName}[${typeOf[String].typeSymbol.fullName}]{ }; ${newName}}"))
  }
}