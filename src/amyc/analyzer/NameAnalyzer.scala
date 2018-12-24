package amyc
package analyzer

import utils._
import ast.{Identifier, NominalTreeModule => N, SymbolicTreeModule => S}

// Name analyzer for Amy
// Takes a nominal program (names are plain strings, qualified names are string pairs)
// and returns a symbolic program, where all names have been resolved to unique Identifiers.
// Rejects programs that violate the Amy naming rules.
// Also populates and returns the symbol table.
object NameAnalyzer extends Pipeline[N.Program, (S.Program, SymbolTable)] {
  def run(ctx: Context)(p: N.Program): (S.Program, SymbolTable) = {
    import ctx.reporter._

    // Step 0: Initialize symbol table
    val table = new SymbolTable

    // Step 1: Add modules to table 
    val modNames = p.modules.groupBy(_.name)
    modNames.foreach { case (name, modules) =>
      if (modules.size > 1) {
        fatal(s"Two modules named $name in program", modules.head.position)
      }
    }

    modNames.keys.toList foreach table.addModule


    // Helper method: will transform a nominal type 'tt' to a symbolic type,
    // given that we are within module 'inModule'.
    def transformType(tt: N.TypeTree, inModule: String): S.Type = {
      tt.tpe match {
        case N.IntType => S.IntType
        case N.BooleanType => S.BooleanType
        case N.StringType => S.StringType
        case N.UnitType => S.UnitType
        case N.ClassType(qn@N.QualifiedName(module, name)) =>
          table.getType(module getOrElse inModule, name) match {
            case Some(symbol) =>
              S.ClassType(symbol)
            case None =>
              fatal(s"Could not find type $qn", tt)
          }
      }
    }
    
    // Helper method: will transform a nominal Literal Pattern type
    // to the appropriate S.LiteralPattern subClass
    def transformLiteral[T](lit : N.Literal[T]) = {
        lit match {
            case N.IntLiteral(x) => S.IntLiteral(x)
            case N.BooleanLiteral(x) => S.BooleanLiteral(x)
            case N.StringLiteral(x) => S.StringLiteral(x)
            case N.UnitLiteral() => S.UnitLiteral()
        }
    }.setPos(lit)
        


    // Step 2: Check name uniqueness of definitions in each module
    p.modules.foreach { case (module) =>
        val defsNames = module.defs.groupBy(_.name)
        defsNames.foreach { case (name, defs) =>
          if (defs.size > 1) {
            fatal(s"Two definitions named $name in the same module", defs.head.position)
          }
        }
    }
      
    // Step 3: Discover types and add them to symbol table
    // Step 4: Discover type constructors, add them to table
    // Step 5: Discover functions signatures, add them to table
    p.modules.foreach{ case (module) =>
        module.defs.foreach{ case (definition) =>
            val owner = module.name
            definition match {
                case N.AbstractClassDef(name) => 
                    table.addType(owner, name)
                case N.CaseClassDef(name, fields, parent) => 
                    val argTypes = fields.map(x => transformType(x, owner))
                    val parentOption = table.getType(owner, parent).getOrElse(
                        fatal(s"Parent type Not Found in Case Class", definition.position))
                    table.addConstructor(owner, name, argTypes, parentOption)
                case N.FunDef(name, params, retType, _) => 
                    val argTypes = params.map{x => transformType(x.tt, owner)}
                    table.addFunction(owner, name, argTypes, transformType(retType, owner))
            } 
        } 
    }

  

    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions
    
    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case p@N.AbstractClassDef(name) =>
        val nameS = table.getType(module, name)
            .getOrElse(fatal(s"Type $name not found"))
        S.AbstractClassDef(nameS).setPos(p)
      case p@N.CaseClassDef(name, _, _) =>
        val (nameS, ConstrSig(argTypes, parent, _)) = table.getConstructor(module, name)
            .getOrElse(fatal(s"Constructor $name in module $module not found"))
        val argTypesS = argTypes.map(x => S.TypeTree(x))
        S.CaseClassDef(nameS, argTypesS, parent).setPos(p)
      case fd: N.FunDef =>
        transformFunDef(fd, module)
    }}.setPos(df)

    def transformFunDef(fd: N.FunDef, module: String): S.FunDef = {
      val N.FunDef(name, params, retType, body) = fd
      val Some((sym, sig)) = table.getFunction(module, name)

      params.groupBy(_.name).foreach { case (name, ps) =>
        if (ps.size > 1) {
          fatal(s"Two parameters named $name in function ${fd.name}", fd)
        }
      }

      val paramNames = params.map(_.name)

      val newParams = params zip sig.argTypes map { case (pd@N.ParamDef(name, tt), tpe) =>
        val s = Identifier.fresh(name)
        S.ParamDef(s, S.TypeTree(tpe).setPos(tt)).setPos(pd)
      }

      val paramsMap = paramNames.zip(newParams.map(_.name)).toMap

      S.FunDef(
        sym,
        newParams,
        S.TypeTree(sig.retType).setPos(retType),
        transformExpr(body)(module, (paramsMap, Map()))
      ).setPos(fd)
    }

    // This function takes as implicit a pair of two maps:
    // The first is a map from names of parameters to their unique identifiers,
    // the second is similar for local variables.
    // Make sure to update them correctly if needed given the scoping rules of Amy
    def transformExpr(expr: N.Expr)
                     (implicit module: String, names: (Map[String, Identifier], Map[String, Identifier])): S.Expr = {
      val (params, locals) = names
      val res = expr match {
        // Variables
        case N.Variable(name: N.Name) =>
          val nameS = locals.get(name)
                        .getOrElse(params.get(name)
                        .getOrElse(fatal(s"Undefined variable $name")))
          S.Variable(nameS)
          
        // Literals
        case N.IntLiteral(value: Int) => S.IntLiteral(value)
        case N.BooleanLiteral(value: Boolean) => S.BooleanLiteral(value)
        case N.StringLiteral(value: String) => S.StringLiteral(value)
        case N.UnitLiteral() => S.UnitLiteral()

        // Binary operators
        case N.Plus(lhs: N.Expr, rhs: N.Expr) => S.Plus(transformExpr(lhs), transformExpr(rhs))
        case N.Minus(lhs: N.Expr, rhs: N.Expr) => S.Minus(transformExpr(lhs), transformExpr(rhs))
        case N.Times(lhs: N.Expr, rhs: N.Expr) => S.Times(transformExpr(lhs), transformExpr(rhs))
        case N.Div(lhs: N.Expr, rhs: N.Expr) => S.Div(transformExpr(lhs), transformExpr(rhs))
        case N.Mod(lhs: N.Expr, rhs: N.Expr) => S.Mod(transformExpr(lhs), transformExpr(rhs))
        case N.LessThan(lhs: N.Expr, rhs: N.Expr) => S.LessThan(transformExpr(lhs), transformExpr(rhs))
        case N.LessEquals(lhs: N.Expr, rhs: N.Expr) => S.LessEquals(transformExpr(lhs), transformExpr(rhs))
        case N.And(lhs: N.Expr, rhs: N.Expr) => S.And(transformExpr(lhs), transformExpr(rhs))
        case N.Or(lhs: N.Expr, rhs: N.Expr) => S.Or(transformExpr(lhs), transformExpr(rhs))
        case N.Equals(lhs: N.Expr, rhs: N.Expr) => S.Equals(transformExpr(lhs), transformExpr(rhs))
        case N.Concat(lhs: N.Expr, rhs: N.Expr) => S.Concat(transformExpr(lhs), transformExpr(rhs))
 
        // Unary operators
        case  N.Not(e: N.Expr) => S.Not(transformExpr(e))
        case  N.Neg(e: N.Expr) => S.Neg(transformExpr(e))

        // Function/ type constructor call
        case N.Call(qname: N.QualifiedName, args: List[N.Expr]) => 
          val moduleS = qname.module.getOrElse(module)
          val argsS = args.map(x => transformExpr(x))
          val (identifier, constrSig) = table.getConstructor(moduleS, qname.name)
                                        .getOrElse(table.getFunction(moduleS, qname.name)
                                        .getOrElse(fatal(s"Call to undefined function/constructor $module.$qname.name")))
          if(constrSig.argTypes.size != args.size)
            fatal(s"Wrong Number of arguments in $module.$qname.name")
         
          S.Call(identifier, argsS)
          
        // The ; operator
        case N.Sequence(e1: N.Expr, e2: N.Expr) => S.Sequence(transformExpr(e1), transformExpr(e2))
          
        // Local variable definition
        case N.Let(df: N.ParamDef, value: N.Expr, body: N.Expr) =>
            if(locals.contains(df.name))
                fatal(s"Local variable $df.name already defined")
            val idName = Identifier.fresh(df.name)
            val paramsDef = S.ParamDef(idName, S.TypeTree(transformType(df.tt, module)))
            S.Let(paramsDef, transformExpr(value), transformExpr(body)(module, (params, locals + (df.name -> idName))))
        
        case N.Var(df: N.ParamDef, value, body: N.Expr) => // Variable definition
            if(locals.contains(df.name))
                fatal(s"Local variable $df.name already defined")
            val idName = Identifier.fresh(df.name, Identifier.ASSIGNABLE)
            val paramsDef = S.ParamDef(idName, S.TypeTree(transformType(df.tt, module)))
            S.Var(paramsDef, transformExpr(value), transformExpr(body)(module, (params, locals + (df.name -> idName))))
            
        case N.Assign(name: N.Name, newValue: N.Expr) => // Variable Assignation
            val nameS = locals.get(name)
                        .getOrElse(params.get(name)
                        .getOrElse(fatal(s"Undefined variable $name")))
            if(nameS.assignable != Identifier.ASSIGNABLE)
                fatal(s"Variable $name is not assignable")

            S.Assign(nameS, transformExpr(newValue))
          
        case N.While(cond: N.Expr, body: N.Expr) => // While loop
            S.While(transformExpr(cond), transformExpr(body))
          
        // If-then-else
        case N.Ite(cond: N.Expr, thenn: N.Expr, elze: N.Expr) => S.Ite(transformExpr(cond), transformExpr(thenn), transformExpr(elze))
          
        // Pattern matching
        case N.Match(scrut, cases) =>
          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = {
            val ret = pat match {
                case N.WildcardPattern() =>  // _
                    (S.WildcardPattern(), Nil)
                case N.IdPattern(name: N.Name) => // x
                    val identifier = Identifier.fresh(name)
                    if(locals.contains(name))
                        fatal(s"$name already defined in the scope")
                    (S.IdPattern(identifier), List((name, identifier)))
                case N.LiteralPattern(lit) => // 42, true
                    (S.LiteralPattern(transformLiteral(lit)), Nil)
                case N.CaseClassPattern(constr: N.QualifiedName, args: List[N.Pattern]) => // C(arg1, arg2)
                    val moduleS = constr.module.getOrElse(module)
                    val argsS = args.map(x => transformPattern(x))
                
                    argsS.foreach{ e =>
                        val names = e._2.map(args => args._1)
                        names.foreach{name =>
                            if(locals.contains(name))
                                fatal(s"$name already defined in the scope")
                        }   
                    }
                    val (identifier, constrSig) = table.getConstructor(module, constr.name)
                                                .getOrElse(fatal(s"Call to undefined constructor $module.$constr.name"))
                    if(constrSig.argTypes.size != args.size)
                        fatal(s"Wrong Number of arguments in $constr.${constr.name}")
                           
                    (S.CaseClassPattern(identifier, argsS.map(_._1)), argsS.map(_._2).flatten)
            }
            ret._1.setPos(pat)
            ret
          }

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)
            S.MatchCase(newPat, transformExpr(rhs)(module, (params, locals ++ moreLocals)))
          }

          S.Match(transformExpr(scrut), cases.map(transformCase))
          
        case N.Error(msg: N.Expr) => S.Error(transformExpr(msg))
      }
      res.setPos(expr)
    }

    // Putting it all together to construct the final program for step 6.
    val newProgram = S.Program(
      p.modules map { case mod@N.ModuleDef(name, defs, optExpr) =>
        S.ModuleDef(
          table.getModule(name).get,
          defs map (transformDef(_, name)),
          optExpr map (transformExpr(_)(name, (Map(), Map())))
        ).setPos(mod)
      }
    ).setPos(p)

    (newProgram, table)

  }
}
