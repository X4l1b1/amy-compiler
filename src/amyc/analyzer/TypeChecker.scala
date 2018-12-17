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
        // Variables
        case Variable(name) => topLevelConstraint(env.get(name).get)

        // Literals
        case IntLiteral(_) => topLevelConstraint(IntType)
        case BooleanLiteral(_) => topLevelConstraint(BooleanType)
        case StringLiteral(_) => topLevelConstraint(StringType)
        case UnitLiteral() => topLevelConstraint(UnitType)

        // Binary operators
        case Plus(lhs, rhs) => topLevelConstraint(IntType) ++ genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType)
        case Minus(lhs, rhs) => topLevelConstraint(IntType) ++ genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType)
        case Times(lhs, rhs) => topLevelConstraint(IntType) ++ genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType)
        case Div(lhs, rhs) => topLevelConstraint(IntType) ++ genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType)
        case Mod(lhs, rhs) => topLevelConstraint(IntType) ++ genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType)
        case LessThan(lhs, rhs) => topLevelConstraint(BooleanType) ++ genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType)
        case LessEquals(lhs, rhs) => topLevelConstraint(BooleanType) ++ genConstraints(lhs, IntType) ++ genConstraints(rhs, IntType)
        case And(lhs, rhs) => topLevelConstraint(BooleanType) ++ genConstraints(lhs, BooleanType) ++ genConstraints(rhs, BooleanType)
        case Or(lhs, rhs) => topLevelConstraint(BooleanType) ++ genConstraints(lhs, BooleanType) ++ genConstraints(rhs, BooleanType)
        case Concat(lhs, rhs) => topLevelConstraint(StringType) ++ genConstraints(lhs, StringType) ++ genConstraints(rhs, StringType)
        case Equals(lhs, rhs) => 
          val typeEquals = TypeVariable.fresh()
          topLevelConstraint(BooleanType) ++ genConstraints(lhs, typeEquals) ++ genConstraints(rhs, typeEquals)

        // Unary operators
        case Not(e) => topLevelConstraint(BooleanType) ++ genConstraints(e, BooleanType)
        case Neg(e) => topLevelConstraint(IntType) ++ genConstraints(e, IntType)

        // Function/ type constructor call
        case Call(qname, args) => 
          val signature = table.getFunction(qname).getOrElse(table.getConstructor(qname).get)
           signature match {
            case FunSig(argTypes, retType, _) =>
              args.zip(argTypes).foldLeft(List[Constraint]()){
                (acc, arg) => acc ++ genConstraints(arg._1, arg._2)
              } ++ topLevelConstraint(retType)
            case ConstrSig(argTypes, _, _) =>
              args.zip(argTypes).foldLeft(List[Constraint]()){
                (acc, arg) => acc ++ genConstraints(arg._1, arg._2)
              } ++ topLevelConstraint(signature.retType)
          }

        // The ; operator
        case Sequence(e1, e2) => 
          val typeE1 = TypeVariable.fresh()
          genConstraints(e1, typeE1) ++ genConstraints(e2, expected)

        // Local constant definition
        case Let(df, value, body) => 
          genConstraints(value, df.tt.tpe) ++ genConstraints(body, expected)(env + (df.name -> df.tt.tpe))
        
        // Local variable definition
        case Var(df, value, body) =>
          genConstraints(value, df.tt.tpe) ++ genConstraints(body, expected)(env + (df.name -> df.tt.tpe))
          
        // Local variable assignement
        case Assign(name, value) =>
          val varType= env.getOrElse(name, UnitType)
          genConstraints(value, varType)
        
        // While Loop
        case While(cond, body) => genConstraints(cond, BooleanType) ++ genConstraints(body, UnitType)
          
        // If-then-else
        case Ite(cond, thenn, elze) =>
          genConstraints(cond, BooleanType) ++ genConstraints(thenn, expected) ++ genConstraints(elze, expected)

        // Pattern matching
        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          def handlePattern(pat: Pattern, scrutExpected: Type):
            (List[Constraint], Map[Identifier, Type]) = 
          {
            pat match {
              case WildcardPattern() =>  // _
                (Nil, Map[Identifier, Type]())

              case IdPattern(name) => // x
                (Nil, Map(name -> scrutExpected))

              case LiteralPattern(lit) => // 42, true
                (genConstraints(lit, scrutExpected), Map[Identifier, Type]())

              case CaseClassPattern(constr, args) => // C(arg1, arg2)
                val signature = table.getConstructor(constr).get
                val argsHandled = args.zip(signature.argTypes).foldLeft((List[Constraint](),  Map[Identifier, Type]())){
                (acc, arg) => 
                  val x = handlePattern(arg._1, arg._2);
                  (acc._1 ++ x._1, acc._2 ++ x._2)
                }
                (argsHandled._1 ++ List(Constraint(signature.retType, scrutExpected, e.position)), argsHandled._2)     
            }
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            patConstraints ++ genConstraints(cse.expr, expected)(env ++ moreEnv)
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))

        // Represents a computational error; prints its message, then exits
        case Error(msg) => genConstraints(msg, StringType)
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
          expected match {
            case TypeVariable(id) => solveConstraints(subst_*(constraints, id, found))
            case _ => 
              if(found != expected){
                error("TypeError: " + found + " does not match " + expected, pos)
              }
              solveConstraints(more)
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
