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

  @Override
  override def constructQname(pTree: NodeOrLeaf[Token]): (QualifiedName, Positioned) = {
    pTree match {
      case Node('QName ::= _, List(id, Node('QNameModule ::= _, List()))) =>
        val (name, pos) = constructName(id)
        (QualifiedName(None, name), pos)
      case Node('QName ::= _, List(id, Node('QNameModule ::= _, List(_, nm)))) =>
        val (module, pos) = constructName(id)
        val (name, _) = constructName(nm)
        (QualifiedName(Some(module), name), pos)
    }
  }

  @Override
  override def constructExpr(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('Expr ::= List('ExprMatch, 'ExprH), List(expMatch, Node('ExprH ::= _, List()))) =>
        constructExprMatch(expMatch)
      case Node('Expr ::= List('ExprMatch, 'ExprH), List(expMatch, Node('ExprH ::= _, List(_, exp)))) =>
        val exprMatch = constructExprMatch(expMatch)
        val expr = constructExpr(exp)
        Sequence(exprMatch, expr)
      case Node('Expr ::= (VAL() :: _), List(Leaf(vt), param, _, value, _, body)) =>
        Let(constructParam(param), constructExprMatch(value), constructExpr(body)).setPos(vt)
      case p => constructExprMatch(p)
    }
  }

  // Helpers functions for Expr construction 
  def constructExprMatch(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprMatch ::= _, List(expOr, Node('ExprMatchH ::= _, List()))) =>
        constructExprOr(expOr)
      case Node('ExprMatch ::= _, List(expOr, Node('ExprMatchH ::= _, List(_, _, cases, _)))) =>
        val scrut = constructExprOr(expOr)
        Match(scrut, constructListMatch(cases, constructCase))
      case p => constructExprOr(p)
    }
  }

  def constructExprOr(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprOr ::= _, List(expAnd, Node('ExprOrH ::= _, List()))) =>
        constructExprAnd(expAnd)
      case Node('ExprOr ::= _, List(expAnd, rightSide)) =>
        val exprAnd = constructExprAnd(expAnd)
        constructOpExpr(exprAnd, rightSide)
      case p => constructExprAnd(p)
    }
  }

  def constructExprAnd(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprAnd ::= _, List(expEq, Node('ExprAndH ::= _, List()))) =>
        constructExprEq(expEq)
      case Node('ExprAnd ::= _, List(expEq, rightSide)) =>
        val exprEq = constructExprEq(expEq)
        constructOpExpr(exprEq, rightSide)
      case p => constructExprEq(p)
    }
  }

  def constructExprEq(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprEq ::= _, List(expLess, Node('ExprEqH ::= _, List()))) =>
        constructExprLess(expLess)
      case Node('ExprEq ::= _, List(expLess, rightSide)) =>
        val exprLess = constructExprLess(expLess)
        constructOpExpr(exprLess, rightSide)
      case p => constructExprLess(p)
    }
  }

  def constructExprLess(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprLess ::= _, List(expAddSub, Node('ExprLessH ::= _, List()))) =>
        constructExprAddSub(expAddSub)
      case Node('ExprLess ::= _, List(expAddSub, rightSide)) =>
        val exprAddSub = constructExprAddSub(expAddSub)
        constructOpExpr(exprAddSub, rightSide)
      case p => constructExprAddSub(p)
    }
  }

  def constructExprAddSub(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprAddSub ::= _, List(expTimesDivMod, Node('ExprAddSubH ::= _, List()))) =>
        constructExprTimesDivMod(expTimesDivMod)
      case Node('ExprAddSub ::= _, List(expTimesDivMod, rightSide)) =>
        val exprTimesDivMod = constructExprTimesDivMod(expTimesDivMod)
        constructOpExpr(exprTimesDivMod, rightSide)
      case p => constructExprTimesDivMod(p)
    }
  }

  def constructExprTimesDivMod(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprTimesDivMod ::= _, List(expUnary, Node('ExprTimesDivModH ::= _, List()))) =>
        constructExprUnary(expUnary)
      case Node('ExprTimesDivMod ::= _, List(expUnary, rightSide)) =>
        val exprUnary = constructExprUnary(expUnary)
        constructOpExpr(exprUnary, rightSide)
      case p => constructExprUnary(p)
    }
  }

  def constructExprUnary(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprUnary ::= List(BANG(), _), List(Leaf(bt), expSpec)) =>
        Not(constructExpr(expSpec)).setPos(bt)
      case Node('ExprUnary ::= List(MINUS(), _), List(Leaf(mt), expSpec)) =>
        Neg(constructExpr(expSpec)).setPos(mt)
      case Node('ExprUnary ::= _, List(expSpec)) =>
        constructExprSpec(expSpec)
      case p => constructExprSpec(p)
    }
  }

  def constructExprSpec(pTree: NodeOrLeaf[Token]): Expr = {
    pTree match {
      case Node('ExprSpec ::= List('Id, 'ExprCallH), List(id, Node('ExprCallH ::= _, List()))) =>
        val (name, pos) = constructName(id)
        Variable(name).setPos(pos)
      case Node('ExprSpec ::= List('Id, 'ExprCallH), List(id, Node('ExprCallH ::= _, List(Node(_, List(_, qnm)), _, as, _)))) =>
        val (module, pos1) = constructName(id)
        val (name, _) = constructName(qnm)
        val (qname, pos) = (QualifiedName(Some(module), name), pos1)
        val args = constructList(as, constructExpr, hasComma = true)
        Call(qname, args).setPos(pos)
      case Node('ExprSpec ::= List('Id, 'ExprCallH), List(id, Node('ExprCallH ::= _, List(Node(_, List()), _, as, _)))) =>
        val (name, pos1) = constructName(id)
        val (qname, pos) = (QualifiedName(None, name), pos1)
        val args = constructList(as, constructExpr, hasComma = true)
        Call(qname, args).setPos(pos1)
      case Node('ExprSpec ::= List('LiteralParen), List(lit)) =>
        constructLiteralParen(lit)
      case Node('ExprSpec ::= List(_, 'ExprParenH), List(Leaf(lparen), Node(_, List(_)))) =>
        UnitLiteral().setPos(lparen)
      case Node('ExprSpec ::= List(_, 'ExprParenH), List(Leaf(lparen), Node(_, List(expr, _)))) =>
        constructExpr(expr).setPos(lparen)
      case Node('ExprSpec ::= (ERROR() :: _), List(Leaf(ert), _, msg, _)) =>
        Error(constructExpr(msg)).setPos(ert)
      case Node('ExprSpec ::= (IF() :: _), List(Leaf(it), _, cond, _, _, thenn, _, _, _, elze, _)) =>
        Ite(
          constructExpr(cond),
          constructExpr(thenn),
          constructExpr(elze)
        ).setPos(it)
    }
  }

  @Override
  override def constructPattern(pTree: NodeOrLeaf[Token]): Pattern = {
    pTree match {
      case Node('Pattern ::= List(UNDERSCORE()), List(Leaf(ut))) =>
        WildcardPattern().setPos(ut)
      case Node('Pattern ::= List('Literal), List(lit)) =>
        val literal = constructLiteral(lit)
        LiteralPattern(literal).setPos(literal)
      case Node('Pattern ::= List('Id, 'PatternH), List(id, Node(_, List()))) =>
        val (name, pos) = constructName(id)
        IdPattern(name).setPos(pos)
      case Node('Pattern ::=  List('Id, 'PatternH), List(id, Node(_, List(Node(_, List(_, qnm)), _, patts, _)))) =>
        val (module, pos1) = constructName(id)
        val (name, _) = constructName(qnm)
        val (qname, pos) = (QualifiedName(Some(module), name), pos1)
        val patterns = constructList(patts, constructPattern, hasComma = true)
        CaseClassPattern(qname, patterns).setPos(pos)
      case Node('Pattern ::=  List('Id, 'PatternH), List(id, Node(_, List(Node(_, List()), _, patts, _)))) =>
        val (name, pos1) = constructName(id)
        val (qname, pos) = (QualifiedName(None, name), pos1)
        val patterns = constructList(patts, constructPattern, hasComma = true)
        CaseClassPattern(qname, patterns).setPos(pos)

    }
  }

  def constructLiteralParen(pTree: NodeOrLeaf[Token]): Literal[_] = {
    pTree match {
      case Node('LiteralParen ::= List(INTLITSENT), List(Leaf(it@INTLIT(i)))) =>
        IntLiteral(i).setPos(it)
      case Node('LiteralParen ::= List(STRINGLITSENT), List(Leaf(st@STRINGLIT(s)))) =>
        StringLiteral(s).setPos(st)
      case Node('LiteralParen ::= _, List(Leaf(tt@TRUE()))) =>
        BooleanLiteral(true).setPos(tt)
      case Node('LiteralParen ::= _, List(Leaf(tf@FALSE()))) =>
        BooleanLiteral(false).setPos(tf)
    }
  }

  def constructListMatch[A](ptree: NodeOrLeaf[Token], constructor: NodeOrLeaf[Token] => A, hasComma: Boolean = false): List[A] = {
    ptree match {
      case Node(_ ::= List('Case, 'CasesH), List(t, Node(_, List()))) => 
        List(constructor(t))
      case Node(_ ::= List('Case, 'CasesH), List(t, ts)) =>
        constructor(t) :: constructListMatch(ts, constructor, hasComma)
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
        if Set('ExprOrH, 'ExprAndH, 'ExprEqH, 'ExprLessH, 'ExprAddSubH, 'ExprTimesDivModH) contains sym =>
        rightNode match {
          case Node(_, List(nextOpd, suf)) => // 'Expr? ::= Expr? ~ 'OpExpr,
            val nextAtom = constructExpr(nextOpd)
            constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf) // captures left associativity
        }
    }
  }

  @Override
  override def constructOp(ptree: NodeOrLeaf[Token]): (Expr, Expr) => Expr = {
    ptree match {
      case Leaf(t) =>
        tokenToExpr(t)
      case Node(_, List(Leaf(t))) =>
        tokenToExpr(t)
    }
  }
}

