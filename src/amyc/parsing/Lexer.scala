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
    case _          => None
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
        // Ignore line by updating nextToken and doing nothing else
        val nextLine = stream.dropWhile{ case (ch, _) => ch != EndOfFile && ch != '\n' }
        nextToken(nextLine)
      } else if (currentChar == '/' && nextChar == '*') {
        // Multi-line comment
        // Drop multiple line until we find pattern "*/"
        def keepDroping(checkSlash : Boolean, curStream : Stream[Input]) : Stream[Input] = {
          curStream match {
            case ('*',_) #:: rest => keepDroping(true, rest)
            case ('/',_) #:: rest => 
              if(checkSlash)
                rest
              else
                keepDroping(false, rest)
            case(EndOfFile,_) #:: rest => 
              ctx.reporter.error("Invalid comment delimiters \n", currentPos)
              curStream
            case (_,_)#:: rest => keepDroping(false, rest)
          }
        }
        nextToken(keepDroping(false, stream.tail.tail))
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
          // Hint: Decide if it's a letter or reserved word (use our infrastructure!),
          // and return the correct token, along with the remaining input stream.
          // Make sure you set the correct position for the token.
          val keyword = keywords(word)
          keywords(word) match {
            case Some(t) =>
              val token = keyword.get
              (token.setPos(currentPos), afterWord)

            case None => 
              val id = ID(word)
              (id.setPos(currentPos), afterWord)
          }
        // Int literal
        case _ if Character.isDigit(currentChar) =>
          // Hint: Use a strategy similar to the previous example.
          // Make sure you fail for integers that do not fit 32 bits.
          val (numChars, afterNum) = stream.span { case (ch, _) =>
            Character.isDigit(ch) || ch == '_'
          }
          try{
              val num = numChars.map(_._1).mkString.toInt
              (INTLIT(num).setPos(currentPos), afterNum)
          }
          catch {
                case e: Exception => 
                  ctx.reporter.error("Invalid literal number. \n")
                  (BAD().setPos(currentPos), afterNum)
          }
         
        // String literal
        case '"' =>
          val (strChars, afterStr) = rest.span { case (ch, _) =>
            ch != '"' && ch != '\n' && ch != EndOfFile  
          }
          val str = strChars.map(_._1).mkString
          if(afterStr.head._1 == '"') {
            (STRINGLIT(str).setPos(currentPos), afterStr.tail)
          }
          else {
            ctx.reporter.error("End of file reached while parsing String litteral.", currentPos)
            (BAD().setPos(currentPos), afterStr.tail)
          }
        case ';'        => useOne(SEMICOLON())
        case '+'        => 
          if(nextChar == '+')
            useTwo(CONCAT())
          else
            useOne(PLUS()) 
        case '-'     => useOne(MINUS())
        case '*'    => useOne(TIMES())
        case '/'      => useOne(DIV())
        case '%'     => useOne(MOD())
        case '<'    => 
          if(nextChar == '=')
            useTwo(LESSEQUALS())
          else
            useOne(LESSTHAN())
        case '&'    => 
          if(nextChar == '&')
            useTwo(AND())
          else{
            ctx.reporter.error("Bad operator \n", currentPos)
            (BAD().setPos(currentPos), rest)
          }
        case '|'       =>
          if(nextChar == '|')
            useTwo(OR())
          else{
            ctx.reporter.error("Bad operator \n", currentPos)
            (BAD().setPos(currentPos), rest)
          }
        case '='      => Some(INT())
          if(nextChar == '=')
            useTwo(EQUALS())
          else if(nextChar == '>')
            useTwo(RARROW())
          else
            useOne(EQSIGN())
        case '!'    => useOne(BANG())
        case '{' => useOne(LBRACE())
        case '}'  => useOne(RBRACE())
        case '('     => useOne(LPAREN())
        case ')'    => useOne(RPAREN())
        case ','      => useOne(COMMA())
        case ':'     => useOne(COLON())
        case '.'    => useOne(DOT())
        case '_'  => useOne(UNDERSCORE())
        case _ => 
          ctx.reporter.error("Bad operator \n", currentPos)
          (BAD().setPos(currentPos), rest)
        
        
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
