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

    // Step 2: Check name uniqueness of definitions in each module
    val moduleDefs = p.modules.map(m => m.defs.groupBy(_.name))
    moduleDefs.foreach(md => md.foreach{
      case (name, defList) =>
        if(defList.size > 1){
           fatal(s"Two or more definitions named $name in  $moduleDefs.name", defList.head.position)
        }
    })

    p.modules.foreach{
      case N.ModuleDef(name, defs, _) =>
        defs.foreach{
          // Step 3: Discover types and add them to symbol table
          case N.AbstractClassDef(classname) => table.addType(name, classname)
          // Step 4: Discover type constructors, add them to table
          case N.CaseClassDef(classname, fields, parentname) =>
            table.getType(name, parentname) match {
              case Some(parent) => 
                val fieldsmap = fields.map(fld => transformType(fld, name))
                table.addConstructor(name, classname, fieldsmap, parent)
              case None =>
                fatal(s"$defs not in $name", defs.head.position)
            }
        // Step 5: Discover functions signatures, add them to table
          case N.FunDef(funcname, params, retType, body) =>
            val paramMap = params.map(param => transformType(param.tt, name))
            val rettype = transformType(retType, name)
            table.addFunction(name, funcname, paramMap, rettype)
          case _ =>
        }
    }

    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions
    
    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case N.AbstractClassDef(name) =>
        transformAbsstractClassDef(name, module)
      case N.CaseClassDef(name, _, _) =>
        transformCaseClassDef(name, module)
      case fd: N.FunDef =>
        transformFunDef(fd, module)
    }}.setPos(df)

    def transformAbsstractClassDef(name: N.Name, module: String): S.ClassOrFunDef = {
      val id = table.getType(module, name).get
      S.AbstractClassDef(id)
    }

    def transformCaseClassDef(name: N.Name, module: String): S.ClassOrFunDef = {
      val (id, constrType) = table.getConstructor(module, name).get
      val ConstrSig(argTypes, parent, _) = constrType
      val sblArgs = argTypes.map(arg => S.TypeTree(arg))
      S.CaseClassDef(id, sblArgs, parent)
}

    def transformFunDef(fd: N.FunDef, module: String): S.FunDef = {
      val N.FunDef(name, params, retType, body) = fd
      val Some((sym, sig)) = table.getFunction(module, name)

      params.groupBy(_.name).foreach { case (name, ps) =>
        if (ps.size > 1) {
          fatal(s"More than one parameters named $name in function ${fd.name}", fd)
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
        case N.Match(scrut, cases) =>
          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = {
            pat match {
              case N.CaseClassPattern(constr, args) =>
                val constrMod = constr.module.getOrElse(module)
                val constrName = constr.name
                val symConstr = table.getConstructor(constrMod, constrName) match {
                  case Some((sbl, sig)) =>
                    if(sig.argTypes.size != args.size)
                      fatal(s"Wrong number of arguments in $constrMod.name", pat)
                    else
                      sbl
                  case None =>
                    fatal(s"Constructor not found :$constrMod.name")

                }
                val transfArgs = args.map(arg => transformPattern(arg))
                val newPatt = transfArgs.map(arg => arg._1)
                val newId = transfArgs.flatMap(arg => arg._2)

                if(newId.map(_._1).distinct.size < newId.size)
                      fatal(s"Multiple definitions for pattern :", pat)
                  (S.CaseClassPattern(symConstr, newPatt).setPos(pat), newId)
              case N.WildcardPattern() =>
                    (S.WildcardPattern().setPos(pat),List())
              case N.LiteralPattern(lit) =>
                val retLit = lit match {
                  case N.IntLiteral(value) => S.IntLiteral(value).setPos(lit)
                  case N.BooleanLiteral(value) => S.BooleanLiteral(value).setPos(lit)
                  case N.StringLiteral(value) => S.StringLiteral(value).setPos(lit)
                  case N.UnitLiteral() => S.UnitLiteral().setPos(lit)
                }
                (S.LiteralPattern(retLit).setPos(pat), Nil)
              case N.IdPattern(name) =>
                val id = Identifier.fresh(name)
                (S.IdPattern(id).setPos(pat), List((name, id)))
            }
          }

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)

            moreLocals.foreach{ 
              case (str, _) =>
                if(locals.contains(str)) 
                  fatal(s"Pattern identifier $str is already defined", pat)
            }
            val newloc = locals ++ moreLocals.toMap
            S.MatchCase(newPat, transformExpr(rhs)(module, (params, newloc))).setPos(cse)
          }

            S.Match(transformExpr(scrut), cases.map(transformCase))

          case N.Call(qname, args) =>
            val callMod = qname.module.getOrElse(module)
            val callName = qname.name
            val csbl = table.getFunction(callMod, callName) match {
              case Some((sbl, sig)) => {
                if(sig.argTypes.size != args.size) fatal(s"Wrong number of arguments for function ${callName}")
                else sbl
              }
              case None => {
                table.getConstructor(callMod, callName) match {
                  case Some((sbl, sig)) => {
                    if(sig.argTypes.size != args.size) fatal(s"Wrong number of arguments for constructor ${callName}")
                    else sbl
                  }
                  case None => fatal(s"$callName doesn't match with function or constructor in module ${callMod}")
                }
              }

            }
            val newArgs = args.map(arg => transformExpr(arg))
            S.Call(csbl, newArgs)
          case N.Sequence(e1, e2) => 
            S.Sequence(transformExpr(e1), transformExpr(e2))
          case N.Let(df, value, body) =>  
            val s = Identifier.fresh(df.name)
            val sTT = S.TypeTree(transformType(df.tt, module))
            val parmDef = S.ParamDef(s, sTT)
            val transVal = transformExpr(value)
            if (locals.contains(df.name)) fatal(s"Variable redefinition of ${df.name}", df.position)
            val newBody = transformExpr(body)(module, (params, locals + (df.name -> s)))
            S.Let(parmDef, transVal, newBody)
          case N.IntLiteral(value) => 
            S.IntLiteral(value)
          case N.BooleanLiteral(value) => 
            S.BooleanLiteral(value)
          case N.StringLiteral(value) => 
            S.StringLiteral(value)
          case N.UnitLiteral() => S.UnitLiteral()
          case N.Not(e) => S.Not(transformExpr(e))
          case N.Neg(e) => S.Neg(transformExpr(e))
          case N.Ite(cond, tthen, eelse) => 
            S.Ite(transformExpr(cond), transformExpr(tthen), transformExpr(eelse))
          case N.Plus(lhs, rhs) => 
            S.Plus(transformExpr(lhs), transformExpr(rhs))
          case N.Minus(lhs, rhs) => 
            S.Minus(transformExpr(lhs), transformExpr(rhs))
          case N.Times(lhs, rhs) => 
            S.Times(transformExpr(lhs), transformExpr(rhs))
          case N.Div(lhs, rhs) => 
            S.Div(transformExpr(lhs), transformExpr(rhs))
          case N.Mod(lhs, rhs) => 
            S.Mod(transformExpr(lhs), transformExpr(rhs))
          case N.LessThan(lhs, rhs) => 
            S.LessThan(transformExpr(lhs), transformExpr(rhs))
          case N.LessEquals(lhs, rhs) => 
            S.LessEquals(transformExpr(lhs), transformExpr(rhs))
          case N.And(lhs, rhs) => 
            S.And(transformExpr(lhs), transformExpr(rhs))
          case N.Or(lhs, rhs) => 
            S.Or(transformExpr(lhs), transformExpr(rhs))
          case N.Equals(lhs, rhs) => 
            S.Equals(transformExpr(lhs), transformExpr(rhs))
          case N.Concat(lhs, rhs) => 
            S.Concat(transformExpr(lhs), transformExpr(rhs))
          case N.Error(msg) => S.Error(transformExpr(msg))
          case N.Variable(name) =>
            val identifier = locals.getOrElse(name, params.getOrElse(name, fatal(s"Variable $name does not exist", expr)))
            S.Variable(identifier)

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
