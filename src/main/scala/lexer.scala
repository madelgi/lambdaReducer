// 
// lexer.scala
//
// A lexer for the lambda calculus
//

package mdel.lambdaReducer;
package lexer;
import java.io.File;
  
// 
// Runtime exceptions
//
case class SyntaxError(message:String,location:String) extends Exception;
//
// Lexical tokens
//
abstract class Token {
  var position:Int = 0;
  var line:Int = 0;
  def report():String = {
    return "Line "+line+", column "+position+":";
  }
}
case class NAMEt(identifier:String) extends Token;
case object ASSIGNt extends Token;
case object SEMIt extends Token;
case object SLASHt extends Token;
case object DOTt extends Token;
case object LPARENt extends Token;
case object RPARENt extends Token;
case object EOFt extends Token;

object lexer {

  //
  // Symbolic "words" and their token equivalents.
  //
  val ops = Map(
    "\\"->SLASHt, 
    ":="->ASSIGNt, 
    "." ->DOTt,
    ";" ->SEMIt );  
  //
  // Token stream support.  Used by the parser.
  //
  var tokens:List[Token] = Nil;
  //
  def initWith(s:String):Unit = {
    scanner.initWith(s);
    tokens = scanner.allTokens();
  }
  //
  def nextToken():Token = {
    return tokens.head;
  }
  //
  def advanceToken():Unit = {
    tokens = tokens.tail;
  } 
  //
  def consumeToken(t:Token):Unit = {
    if (nextToken() == t) {
      advanceToken();
    } else {
      throw new SyntaxError("Unexpected "+nextToken()+" token.  Expecting "+t+".",nextToken().report());
    }
  }
  //
  def consumeNAMEt():String = {
    nextToken() match {
      case NAMEt(n) => {
        advanceToken();
        return n;
      }
      case t =>
        throw new SyntaxError("Unexpected "+t+" token.  Expecting NAME.",t.report());
    }
  }
  //
  // Lexical analyzer, handles Char sequences of ML code.
  //
  object scanner {
    var stream:List[Char] = Nil;
    var position = 1;
    var line = 1;
    var startp = 1;
    var startl = 1;
    //
    def initWith(s:String):Unit = {
      stream = s.toList;
    }
    //
    def allTokens():List[Token] = {
      val t:Token = emit(scan());
      if (isDone()) {
        return t::EOFt::Nil;
      } else {
        return t::allTokens(); 			     
      }
    }
    //
    def isDone():Boolean = {
      return isAtEOF();
    }
    //
    def isAtEOF():Boolean = {
      return stream == Nil;
    }
    //
    def isAtAlpha():Boolean = {
      return (!isAtEOF() && 
        ((stream.head >= 'a' && stream.head <= 'z')
         || (stream.head >= 'A' && stream.head <= 'Z')));
    }
    //
    def isAtDigit():Boolean = {
      return (!isAtEOF() && 
        (stream.head >= '0' && stream.head <= '9'));
    }
    //
    def isAtSymbol():Boolean = {
      return (!isAtEOF() && ("\\.:=;").toList.contains(stream.head));
    }
    //
    def advance():Unit = {
      if (stream.head == '\n') {
        position = 1; 
        line = line + 1;
      } else if (stream.head == '\t') {
        position = position + 4;
      } else {
        position = position + 1;
      }
      stream = stream.tail;
    }
    //
    def mark():Unit = {
      startp = position;
      startl = line;
    }
    //
    def emit(t:Token):Token = {
      t.position = startp;
      t.line = startl;
      return t;
    }
    //
    def report():String = {
      return "Line "+line+", column "+position+":";
    }
    //
    def scan():Token = {
      mark();
      stream match {

        case Nil => EOFt

        // comment start
        case '('::'*'::_ => { scanComment(); scan() }

        // sub-scanned items that produce tokens
        case c::_ if (isAtAlpha()) => scanWord();
        case c::_ if (isAtSymbol()) => scanOp();

        // parentheses
        case '('::_ => { advance(); LPARENt }
        case ')'::_ => { advance(); RPARENt }

        // whitespace
        case ' '::_ => { advance(); scan() }
        case '\t'::_ => { advance(); scan() }
        case '\n'::_ => { advance(); scan() }
        case '\r'::_ => { advance(); scan() }

      }
    }
    //
    def scanOp():Token = {
      if (stream.head == '.') {
        advance();
        return DOTt;
      } else if (stream.head == '\\') {
        advance();
        return SLASHt;
      } else if (stream.head == ';') {
        advance();
        return SEMIt;
      } else if (stream.head == ':') {
        advance();
        if (stream.head == '=') {
          advance();
          return ASSIGNt;
        }
      }
      throw new SyntaxError("Unrecognized operator.",report());
    }
    //
    def scanWord():Token = {
      var word:String = "";
      while (isAtAlpha()) {
        word = word + stream.head;
        advance();
      }
      while (isAtDigit()) {
        word = word + stream.head;
        advance();
      }
      return NAMEt(word);
    }
    //
    def scanComment():Unit = {
      var depth:Int = 0;
      do {
        stream match {
          case Nil => throw new SyntaxError("Unclosed comment.",report());
          case '('::'*'::_ => { advance(); advance(); depth = depth+1; }
          case '*'::')'::_ => { advance(); advance(); depth = depth-1; }
          case _ => advance();
        }
      } while (depth > 0);
    }
  }
}
