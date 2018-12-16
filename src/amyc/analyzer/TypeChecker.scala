package amyc
package analyzer

import utils._
import ast.SymbolicTreeModule._
import ast.Identifier

// The type checker for Amy
// Takes a symbolic program and rejects it if it does not follow the Amy typing rules.
object TypeChecker extends Pipeline[(Program, SymbolTable), (Program, SymbolTable)] {

  def run(ctx: Context)(v: (Program, SymbolTable)): (Program, SymbolTable) = {
    import ctx.reporter._

    val (program, table) = v

    case class Constraint(found: Type, expected: Type, pos: Position)

    // Represents a type variable.
    // It extends Type, but it is meant only for internal type checker use,
    //  since no Amy value can have such type.
    case class TypeVariable private (id: Int) extends Type
    object TypeVariable {
      private val c = new UniqueCounter[Unit]
      def fresh(): TypeVariable = TypeVariable(c.next(()))
    }

    // Generates typing constraints for an expression `e` with a given expected type.
    // The environment `env` contains all currently available bindings (you will have to
    //  extend these, e.g., to account for local variables).
    // Returns a list of constraints among types. These will later be solved via unification.
    def genConstraints(e: Expr, expected: Type)(implicit env: Map[Identifier, Type]): List[Constraint] = {
      // This helper returns a list of a single constraint recording the type
      //  that we found (or generated) for the current expression `e`
      def topLevelConstraint(found: Type): List[Constraint] =
        List(Constraint(found, expected, e.position))

      e match {
        
        case IntLiteral(_) =>
          	topLevelConstraint(IntType)
        case BooleanLiteral(_) =>
        	topLevelConstraint(BooleanType)
        case StringLiteral(_) =>
        	topLevelConstraint(StringType)
        case UnitLiteral() =>
        	topLevelConstraint(UnitType)

        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          def handlePattern(pat: Pattern, scrutExpected: Type):
            (List[Constraint], Map[Identifier, Type]) =
          {
            pat match {
            	case WildcardPattern() =>
            		(List(), env)
            	case IdPattern(name) =>
            		val nenv = env + (name -> scrutExpected)
            		(List(), nenv)
            	case LiteralPattern(lit) =>
            		(genConstraints(lit, scrutExpected), env)
            	case CaseClassPattern(constr, args) =>
            		val constrSig = table.getConstructor(constr).get
            		val ConstrSig(argType: List[Type], _, _) = table.getConstructor(constr).get
            		//for(idx <- args.indices) handlePattern(args(idx), argType(idx))
                // Debug ce truc là, faire une liste avec les retour de handlePattern,
                    //args.zip(argsT).map{case (arg, argt) => handlePattern(arg, argt)}.flatten ++ topLevelConstraint(retT)

                var newConstr = args.zip(argType).map{case (arg, argt) => handlePattern(arg, argt)}// ++ , Map())
                //newConstr.unzip._1.flatten//(0)// ++ List(Constraint(constrSig.retType, scrutExpected, pat.position)))
                //(newConstr.map(tuple=>tuple._1), newConstr.map(tuple => tuple._2))
                newConstr.foldLeft((List[Constraint](), Map[amyc.ast.Identifier,amyc.ast.SymbolicTreeModule.Type]())){
                	(acc, el) => 
                	
                	(acc._1 ++ el._1, acc._2 ++ el._2)
                				
                }


            }
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            genConstraints(cse.expr, expected)(moreEnv) ++ patConstraints
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))

        case Plus(lhs, rhs) =>
        	genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType) ++ topLevelConstraint(IntType)
        case Minus(lhs, rhs) =>
        	genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType) ++ topLevelConstraint(IntType)
        case Times(lhs, rhs) =>
        	genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType) ++ topLevelConstraint(IntType)
        case Div(lhs, rhs) =>
        	genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType) ++ topLevelConstraint(IntType)
        case Mod(lhs, rhs) =>
        	genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType) ++ topLevelConstraint(IntType)

        case And(lhs, rhs) =>
        	genConstraints(lhs, BooleanType) ++ genConstraints(rhs, BooleanType) ++ topLevelConstraint(BooleanType)
        case Or(lhs, rhs) =>
        	genConstraints(lhs, BooleanType) ++ genConstraints(rhs, BooleanType) ++ topLevelConstraint(BooleanType)

        case LessThan(lhs, rhs) =>
        	genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType) ++ topLevelConstraint(BooleanType)
        case LessEquals(lhs, rhs) =>
        	genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType) ++ topLevelConstraint(BooleanType)
        case Concat(lhs, rhs) =>
        	genConstraints(lhs, StringType) ++ genConstraints(rhs, StringType) ++ topLevelConstraint(StringType)
        
        case Equals(lhs, rhs) =>
          // HINT: Take care to implement the specified Amy semantics
          val st = TypeVariable.fresh()
          genConstraints(lhs, st) ++ genConstraints(rhs, st) ++ topLevelConstraint(BooleanType)
          
        case Not(b) =>
        	genConstraints(b, BooleanType) ++ topLevelConstraint(BooleanType)

        case Neg(b) =>
        	genConstraints(b, IntType) ++ topLevelConstraint(IntType)

        case Ite(cond, thenn, eelse) =>
        	genConstraints(cond, BooleanType) ++ genConstraints(thenn, expected) ++ genConstraints(eelse, expected)
        
        case Let(df, value, body) =>
        	val nenv = env + (df.name -> df.tt.tpe)
        	genConstraints(value, expected) ++ genConstraints(body, expected)(nenv)

        case Variable(name) =>
        	topLevelConstraint(env.get(name).get)

       	case Sequence(head, tail) =>
       		genConstraints(head, TypeVariable.fresh()) ++ genConstraints(tail, expected) 

       	case Call(qname, args) =>
       		val constr = table.getConstructor(qname).orNull
       		if(constr == null){
       			val FunSig(argsT, retT, _) = table.getFunction(qname).get
            args.zip(argsT).map{case (arg, argt) => genConstraints(arg, argt)}.flatten ++ topLevelConstraint(retT)
       		}
       		else{
       			val ConstrSig(argsT: List[Type], _, _) = table.getConstructor(qname).get
            args.zip(argsT).map{case (arg, argt) => genConstraints(arg, argt)}.flatten ++ topLevelConstraint(constr.retType)
       		}
       	case Error(m) =>
        	genConstraints(m, StringType)
      }

    }


    // Given a list of constraints `constraints`, replace every occurence of type variable
    //  with id `from` by type `to`.
    def subst_*(constraints: List[Constraint], from: Int, to: Type): List[Constraint] = {
      // Do a single substitution.
      def subst(tpe: Type, from: Int, to: Type): Type = {
        tpe match {
          case TypeVariable(`from`) => to
          case other => other
        }
      }

      constraints map { case Constraint(found, expected, pos) =>
        Constraint(subst(found, from, to), subst(expected, from, to), pos)
      }
    }

    // Solve the given set of typing constraints and
    //  call `typeError` if they are not satisfiable.
    // We consider a set of constraints to be satisfiable exactly if they unify.
    def solveConstraints(constraints: List[Constraint]): Unit = {
      constraints match {
        case Nil => ()
        case Constraint(found, expected, pos) :: more =>
          // HINT: You can use the `subst_*` helper above to replace a type variable
          //       by another type in your current set of constraints.
          found match {
          	case TypeVariable(i) =>
          		val new_constraints = subst_*(constraints, i, expected)
          		solveConstraints(new_constraints)
          	case _ =>
          		expected match {
          			case TypeVariable(i) =>
          				val new_constraints = subst_*(constraints, i, found)
          				solveConstraints(new_constraints)
          			case _ =>
          				if(found != expected)
          					error(s"Type error ${found}, ${expected}", pos)
          				solveConstraints(more)
          		}
          }
      }
    }

    // Putting it all together to type-check each module's functions and main expression.
    program.modules.foreach { mod =>
      // Put function parameters to the symbol table, then typecheck them against the return type
      mod.defs.collect { case FunDef(_, params, retType, body) =>
        val env = params.map{ case ParamDef(name, tt) => name -> tt.tpe }.toMap
        solveConstraints(genConstraints(body, retType.tpe)(env))
      }

      // Type-check expression if present. We allow the result to be of an arbitrary type by
      // passing a fresh (and therefore unconstrained) type variable as the expected type.
      val tv = TypeVariable.fresh()
      mod.optExpr.foreach(e => solveConstraints(genConstraints(e, tv)(Map())))
    }

    v

  }
}
