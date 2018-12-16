package amyc
package parsing

import grammarcomp.parsing._
import utils.Positioned
import ast.NominalTreeModule._
import Tokens._

// Implements the translation from parse trees to ASTs for the LL1 grammar,
// that is, this should correspond to Parser.amyGrammarLL1.
// We extend the plain ASTConstructor as some things will be the same -- you should
// override whatever has changed. You can look into ASTConstructor as an example.
class ASTConstructorLL1 extends ASTConstructor {

  // TODO: Override methods from ASTConstructor as needed
  override def constructQname(pTree: NodeOrLeaf[Token]): (QualifiedName, Positioned) = {
    pTree match {
      case Node('QName ::= _, List(id, qnamest)) =>
        val (notEmpty, name) = constructQnameSt(qnamest)
        if(notEmpty){
          val (module, pos) = constructName(id)
          (QualifiedName(Some(module), name), pos)
        }
        else{
          val (name, pos) = constructName(id)
          (QualifiedName(None, name), pos)
        }
    }
  }

    def constructQnameSt(pTree: NodeOrLeaf[Token]): (Boolean, String) = {
      pTree match {
        case Node('QNameSt ::= _, List(_, id)) =>
          val (name, pos) = constructName(id)
          (true, name)
        case _ =>
          (false, null)
        }
    }

  override def constructExpr(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('Expr ::= _, List(Leaf(vt), param, _, expr2, _, expr)) =>
        Let(constructParam(param), constructE2(expr2), constructExpr(expr)).setPos(vt)
      case Node('Expr ::= _, List(e2, e1hlpr)) =>
        val (notEmpty, etail) = constructE1Hlpr(e1hlpr)
        if(notEmpty){
          val ehead = constructE2(e2)
          Sequence(ehead, etail).setPos(ehead)
        }
        else{
          constructE2(e2)
        }
      case p => constructE2(p)

    }
  }
      def constructE1Hlpr(pTree: NodeOrLeaf[Token]): (Boolean, Expr) = {
          pTree match {
            case Node('E1Hlpr ::= _, List(_, expr)) =>
              (true, constructExpr(expr))
            case _ =>
              (false, null)
          }
      }

    def constructE2(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E2 ::= _, List(e3, Node('E2Hlpr ::= _, List()))) =>
              constructE3(e3)
            case Node('E2 ::= _, List(e3, Node('E2Hlpr ::= _, List(_,_,cases,_)))) =>
              val scrut = constructE3(e3)
              Match(scrut, constructCases(cases)).setPos(scrut)
            case others =>
              constructE3(others)
          }
    }

    def constructE3(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E3 ::= _, List(e4, Node('E3Hlpr ::= _, List()))) =>
              constructE4(e4)
            case Node('E3 ::= _,List(e4, e3hlpr)) =>
              val expr4 = constructE4(e4)
              constructOpExpr(expr4, e3hlpr)
            case others =>
              constructE4(others)
          }
    }

    def constructE4(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E4 ::= _, List(e5, Node('E4Hlpr ::= _, List()))) =>
              constructE5(e5)
            case Node('E4 ::= _,List(e5, e4hlpr)) =>
              val expr5 = constructE5(e5)
              constructOpExpr(expr5, e4hlpr)
            case others =>
              constructE5(others)
          }
    }

    def constructE5(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E5 ::= _, List(e6, Node('E5Hlpr ::= _, List()))) =>
              constructE6(e6)
            case Node('E5 ::= _,List(e6, e5hlpr)) =>
              val expr6 = constructE6(e6)
              constructOpExpr(expr6, e5hlpr)
            case others =>
              constructE6(others)
          }
    }

    def constructE6(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E6 ::= _, List(e7, Node('E6Hlpr ::= _, List()))) =>
              constructE7(e7)
            case Node('E6 ::= _,List(e7, e6hlpr)) =>
              val expr7 = constructE7(e7)
              constructOpExpr(expr7, e6hlpr)
            case others =>
              constructE7(others)
          }
    }

    def constructE7(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E7 ::= _, List(e8, Node('E7Hlpr ::= _, List()))) =>
              constructE8(e8)
            case Node('E7 ::= _,List(e8, e7hlpr)) =>
              val expr8 = constructE8(e8)
              constructOpExpr(expr8, e7hlpr)
            case others =>
              constructE8(others)
          }
    }

    def constructE8(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E8 ::= _, List(e9, Node('E8Hlpr ::= _, List()))) =>
              constructE9(e9)
            case Node('E8 ::= _,List(e9, e8hlpr)) =>
              val expr9 = constructE9(e9)
              constructOpExpr(expr9, e8hlpr)
            case others =>
              constructE9(others)
          }
    }

    def constructE9(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E9 ::=  List(BANG(), _), List(Leaf(l), e10)) =>
              Not(constructE10(e10)).setPos(l)
            case Node('E9 ::=  List(MINUS(),_), List(Leaf(l), e10)) =>
              Neg(constructE10(e10)).setPos(l)
            case Node('E9 ::= _, List(e10)) =>
              constructE10(e10)
          }
    }

    def constructE10(pTree: NodeOrLeaf[Token]): Expr = {
          pTree match {
            case Node('E10 ::= List('Id, 'QNameHlpr), List(id, Node('QNameHlpr ::= _, List()))) =>
              val (qname, pos) = constructName(id)
              Variable(qname).setPos(pos)
            case Node('E10 ::= List('Id, 'QNameHlpr), List(id, qnamehlpr)) =>
              val (notEmpty, qid, qvals) = constructQNameHlpr(qnamehlpr)
              if(notEmpty){
                val (mod, pos) = constructName(id)
                Call(QualifiedName(Some(mod), qid.get), qvals).setPos(pos)
              }
              else{
                 val (name, pos) = constructName(id)
                 Call(QualifiedName(None,name), qvals).setPos(pos)
              }
            case Node('E10 ::= List('LiteralHlpr), List(literals)) =>
              constructLitteralHlpr(literals)
            case Node('E10 ::= List(LPAREN(), _), List(Leaf(p@LPAREN()), parentHlpr)) =>
              val (notEmpty, expr) = constructParenHlpr(parentHlpr)
              if(notEmpty)
                expr.setPos(p)
              else
                UnitLiteral()setPos(p)
            case Node('E10 ::= (ERROR() :: _ ), List(Leaf(p), _, errmsg, _)) =>
                Error(constructExpr(errmsg)).setPos(p)
            case Node('E10 ::= (IF() :: _), List(Leaf(p), _, cond, _, _, tthen, _, _, _, eelse, _)) =>
                Ite(
                  constructExpr(cond),
                  constructExpr(tthen),
                  constructExpr(eelse)
              ).setPos(p)
              
          }
    }

    override def constructPattern(pTree: NodeOrLeaf[Token]) : Pattern = {
        pTree match {
          case Node('Pattern ::= List(UNDERSCORE()), List(Leaf(ut))) =>
            WildcardPattern().setPos(ut)
          case Node('Pattern ::= List('Literal), List(lit)) =>
            val literal = constructLiteral(lit)
            LiteralPattern(literal).setPos(literal)
          case Node('Pattern ::= List('Id, 'PaternSt), List(id, Node(_, List()))) =>
            val (name, pos) = constructName(id)
            IdPattern(name).setPos(pos) 
          case Node('Pattern ::=  List('Id, 'PatternH), List(id, Node(_, List(Node(_, List(_, qnam)), _, patts, _)))) =>
            val (mod, pos) = constructName(id)
            val (name, _) = constructName(qnam)
            val (qname, pos2) = (QualifiedName(Some(mod), name), pos)
            CaseClassPattern(qname, constructList(patts, constructPattern, hasComma = true)).setPos(pos2)
          case Node('Pattern ::=  List('Id, 'PatternH), List(id, Node(_, List(Node(_, List()), _, patts, _)))) =>
            val (name, pos1) = constructName(id)
            val (qname, pos) = (QualifiedName(None, name), pos1)
            val patterns = constructList(patts, constructPattern, hasComma = true)
            CaseClassPattern(qname, patterns).setPos(pos) 
        }
    }

    def constructQNameHlpr(pTree: NodeOrLeaf[Token]) : (Boolean, Option[String], List[Expr]) = {
          pTree match {
            case Node('QNameHlpr ::= _, List(qnamest, _, args, _)) =>
              val (notEmpty, name) = constructQnameSt(qnamest)
              if(notEmpty)
                (true, Some(name), constructList(args, constructExpr, hasComma = true))
              else
                (false, None, constructList(args, constructExpr, hasComma = true))
            case _ =>
              (false, null, null)

          }
    }

    def constructCases(ptree: NodeOrLeaf[Token]): List[MatchCase] = {
    ptree match {
      case Node(_ ::= List('Case, 'CaseSt), List(t, Node(_, List()))) => 
        List(constructCase(t))
      case Node(_ ::= List('Case, 'CaseSt), List(t, ts)) =>
        constructCase(t) :: constructCaseSt(ts)
    }
  }

   def constructCaseSt(ptree: NodeOrLeaf[Token]): List[MatchCase] = {
    ptree match {
      case Node('CasesSt ::= ('Cases :: Nil), List(cases)) => constructCases(cases)
      case Node('CasesSt ::= _, _) => Nil // epsilon case
    }
  }


    def constructLitteralHlpr(pTree: NodeOrLeaf[Token]) : Literal[_] = {
      pTree match {
      case Node('LiteralHlpr ::= List(INTLITSENT), List(Leaf(p@INTLIT(i)))) =>
        IntLiteral(i).setPos(p)
      case Node('LiteralHlpr ::= List(STRINGLITSENT), List(Leaf(p@STRINGLIT(s)))) =>
        StringLiteral(s).setPos(p)
      case Node('LiteralHlpr ::= _, List(Leaf(p@TRUE()))) =>
        BooleanLiteral(true).setPos(p)
      case Node('LiteralHlpr ::= _, List(Leaf(p@FALSE()))) =>
        BooleanLiteral(false).setPos(p)
      }
    }

    def constructParenHlpr(pTree: NodeOrLeaf[Token]) : (Boolean, Expr) = {
      pTree match {
        case Node('ParenHlpr ::= List(RPAREN()), List(_)) =>
        (false, null)
      case Node('ParenHlpr ::= _, List(expr, _)) =>
        (true, constructExpr(expr))
      }
    }

    override def constructOp(ptree: NodeOrLeaf[Token]): (Expr, Expr) => Expr = {
    ptree match {
      case Leaf(t) =>
        tokenToExpr(t)
      case Node(_, List(Leaf(t))) =>
        tokenToExpr(t)
    }
}
  // Important helper method:
  // Because LL1 grammar is not helpful in implementing left associativity,
  // we give you this method to reconstruct it.
  // This method takes the left operand of an operator (leftopd)
  // as well as the tree that corresponds to the operator plus the right operand (ptree)
  // It parses the right hand side and then reconstruct the operator expression
  // with correct associativity.
  // If ptree is empty, it means we have no more operators and the leftopd is returned.
  // Note: You may have to override constructOp also, depending on your implementation
  def constructOpExpr(leftopd: Expr, ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node(_, List()) => //epsilon rule of the nonterminals
        leftopd
      case Node(sym ::= _, List(op, rightNode))
        if Set('E3Hlpr, 'E4Hlpr, 'E5Hlpr, 'E6Hlpr, 'E7Hlpr, 'E8Hlpr) contains sym =>
        rightNode match {
          case Node(_, List(nextOpd, suf)) => // 'Expr? ::= Expr? ~ 'OpExpr,
            val nextAtom = constructExpr(nextOpd)
            constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf) // captures left associativity
        }
    }
  }

}

