package amyc
package parsing

import utils._
import scala.io.Source
import java.io.File

// The lexer for Amy.
// Transforms an iterator coming from scala.io.Source to a stream of (Char, Position),
// then uses a functional approach to consume the stream.
object Lexer extends Pipeline[List[File], Stream[Token]] {
  import Tokens._

  /** Maps a string s to the corresponding keyword,
    * or None if it corresponds to no keyword
    */
  private def keywords(s: String): Option[Token] = s match {
    case "abstract" => Some(ABSTRACT())
    case "Boolean"  => Some(BOOLEAN())
    case "case"     => Some(CASE())
    case "class"    => Some(CLASS())
    case "def"      => Some(DEF())
    case "else"     => Some(ELSE())
    case "error"    => Some(ERROR())
    case "extends"  => Some(EXTENDS())
    case "false"    => Some(FALSE())
    case "if"       => Some(IF())
    case "Int"      => Some(INT())
    case "match"    => Some(MATCH())
    case "object"   => Some(OBJECT())
    case "String"   => Some(STRING())
    case "true"     => Some(TRUE())
    case "Unit"     => Some(UNIT())
    case "val"      => Some(VAL())
    case "var"      => Some(VAR()) // Variable Token
    case "while"      => Some(WHILE()) // Variable Token
    case _          => None
  }

  /** Maps a character c to the corresponding Operator 
    * or Delimiter, None if there is no match
    */
  private def oneCharacterTokens(c: Char) = c match {
      /* Operators */
      case ';' => Some(SEMICOLON())  // ;
      case '-' => Some(MINUS())      // -
      case '*' => Some(TIMES())      // *
      case '/' => Some(DIV())        // /
      case '%' => Some(MOD())        // %
      case '!' => Some(BANG())       // !

      /* Delimiters and wildcard */
      case '{' => Some(LBRACE())     // {
      case '}' => Some(RBRACE())     // }
      case '(' => Some(LPAREN())     // (
      case ')' => Some(RPAREN())     // )
      case ',' => Some(COMMA())      // ,
      case ':' => Some(COLON())      // :
      case '.' => Some(DOT())        // .
      case '_' => Some(UNDERSCORE()) // _
      case _ => None
  }

  private def lexFile(ctx: Context)(f: File): Stream[Token] = {
    import ctx.reporter._

    // Special character which represents the end of an input file
    val EndOfFile: Char = scala.Char.MaxValue

    val source = Source.fromFile(f)

    // Useful type alias:
    // The input to the lexer will be a stream of characters,
    // along with their positions in the files
    type Input = (Char, Position)

    def mkPos(i: Int) = Position.fromFile(f, i)

    // The input to the lexer
    val inputStream: Stream[Input] =
      source.toStream.map(c => (c, mkPos(source.pos))) #::: Stream((EndOfFile, mkPos(source.pos)))

    /** Gets rid of whitespaces and comments and calls readToken to get the next token.
      * Returns the first token and the remaining input that did not get consumed
      */
    @scala.annotation.tailrec
    def nextToken(stream: Stream[Input]): (Token, Stream[Input]) = {
      require(stream.nonEmpty)

      val (currentChar, currentPos) #:: rest = stream

      // Use with care!
      def nextChar = rest.head._1

      if (Character.isWhitespace(currentChar)) {
        nextToken(stream.dropWhile{ case (c, _) => Character.isWhitespace(c) } )
      } else if (currentChar == '/' && nextChar == '/') {
        // Single-line comment
        val newStream = stream.dropWhile{ case (c, _) => (c != '\n' && c != EndOfFile)}
        if(newStream.head._1 == EndOfFile)
          nextToken(newStream)
        else 
          nextToken(newStream.tail)
        
      } else if (currentChar == '/' && nextChar == '*') {
        // Multi-line comment
        def removeMultiLineComments(stream: Stream[Input]): Stream[Input] = {
          val newStream = stream.dropWhile { case (c, _) => c != '*' && c != EndOfFile}
          if (newStream.head._1 == EndOfFile){
              ctx.reporter.error("Multi-line comment never closed !", currentPos)
              newStream
          }
          else if (newStream.tail.head._1 == '/')
            newStream.tail.tail
          else 
            removeMultiLineComments(newStream.tail)
        }    

        nextToken(removeMultiLineComments(stream.tail.tail)) 
      } else {
        readToken(stream)
      }
    }

    /** Reads the next token from the stream. Assumes no whitespace or comments at the beginning.
      * Returns the first token and the remaining input that did not get consumed.
      */
    def readToken(stream: Stream[Input]): (Token, Stream[Input]) = {
      require(stream.nonEmpty)

      val (currentChar, currentPos) #:: rest = stream

      // Use with care!
      def nextChar = rest.head._1

      // Returns input token with correct position and uses up one character of the stream
      def useOne(t: Token) = (t.setPos(currentPos), rest)
      // Returns input token with correct position and uses up two characters of the stream
      def useTwo(t: Token) = (t.setPos(currentPos), rest.tail)

      currentChar match {
        case `EndOfFile` => useOne(EOF())

        // Reserved word or Identifier
        case _ if Character.isLetter(currentChar) =>
          val (wordLetters, afterWord) = stream.span { case (ch, _) =>
            Character.isLetterOrDigit(ch) || ch == '_'
          }
          val word = wordLetters.map(_._1).mkString
          
          keywords(word) match {
            case Some(t) => (t.setPos(currentPos), afterWord)
            case _ => 
              val newStream = afterWord.dropWhile{ case (c, _) => Character.isWhitespace(c)}
              if (newStream.head._1 != '=' || newStream.tail.head._1 == '=' || newStream.tail.head._1 == '>' || afterWord.tail.dropWhile{ case (c, _) => Character.isWhitespace(c)} == '{'){
                (ID(word).setPos(currentPos), afterWord)
              }
              else{
                (ASSIGN(word).setPos(currentPos), afterWord)
              }
          }

        // Int literal
        case _ if Character.isDigit(currentChar) =>
          val (digitsWord, afterWord) = stream.span { case (ch, _) =>
            Character.isDigit(ch)
          }
          try{
            val digits = digitsWord.map(_._1).mkString.toInt
            (INTLIT(digits).setPos(currentPos), afterWord)
          } catch {
            case _:Exception => 
              ctx.reporter.error("Wrong Int format, may be an overflow", currentPos)
              (BAD().setPos(currentPos), afterWord)
          }

        // String literal
        case '"' =>
          val (stringLiteral, afterWord) = rest.span { case (ch, _) => ch != '"' && ch != EndOfFile && ch != '\n'}

          if(afterWord.head._1 == EndOfFile || afterWord.head._1 == '\n'){
              ctx.reporter.error("String Literal never closed !", currentPos)
              (BAD().setPos(currentPos), afterWord)
          }
          else {
            val string = stringLiteral.map(_._1).mkString
            (STRINGLIT(string).setPos(currentPos), afterWord.tail)
          }

        // Addition or concat
        case '+' =>
          if(nextChar == '+')
            useTwo(CONCAT())
          else
            useOne(PLUS())

        // less or leq
        case '<' =>
          if(nextChar == '=')
            useTwo(LESSEQUALS())
          else
            useOne(LESSTHAN())

        // logical AND
        case '&' => 
          if (nextChar == '&')
            useTwo(AND())
          else {
            ctx.reporter.error("Not found: value '&'", currentPos)
            useOne(BAD())
          }

        // logical OR
        case '|' =>
          if (nextChar == '|')
            useTwo(OR())
          else {
            ctx.reporter.error("Not found: value '|'", currentPos)
            useOne(BAD())
          }

        // Equal, affectation or right arrow
        case '=' =>
          if(nextChar == '=')
            useTwo(EQUALS())
          else if(nextChar == '>')
            useTwo(RARROW())
          else 
            useOne(EQSIGN())

        // All the tokens with one character and BAD entries
        case c =>
          oneCharacterTokens(currentChar) match {
            case Some(t) => useOne(t)
            case _ => 
              ctx.reporter.error("Invalid character: " + c, currentPos)
              useOne(BAD())
          }
      }
    }

    // To lex a file, call nextToken() until it returns the empty Stream as "rest"
    def tokenStream(s: Stream[Input]): Stream[Token] = {
      if (s.isEmpty) Stream()
      else {
        val (token, rest) = nextToken(s)
        token #:: tokenStream(rest)
      }
    }

    tokenStream(inputStream)
  }

  // Lexing all input files means putting the tokens from each file one after the other
  def run(ctx: Context)(files: List[File]): Stream[Token] = {
    files.toStream flatMap lexFile(ctx)
  }
}

/** Extracts all tokens from input and displays them */
object DisplayTokens extends Pipeline[Stream[Token], Unit] {
  def run(ctx: Context)(tokens: Stream[Token]): Unit = {
    tokens.toList foreach { t => println(s"$t(${t.position.withoutFile})") }
  }
}
