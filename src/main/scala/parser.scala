//
// parser.scala
//
// A parser for the lambda calculus
//

package mdel.lambdaReducer;
package parser;

import java.io.File;
import _root_.mdel.lambdaReducer.lexer._;

  
//
// abstract syntax terms
//
abstract class Term;
case class LAM(formal:String,body:Term) extends Term {
  override def toString:String = "\\"+formal+"."+body;
}
case class APP(left:Term,right:Term) extends Term {
  override def toString:String = {
    (left,right) match {
      case (LAM(_,_),VAR(_)) => "("+left+") "+right
      case (LAM(_,_),_) => "("+left+") ("+right+")"
      case (_,VAR(_)) => left + " " + right
      case (_,_) => left+" ("+right+")"
    }
  }
}
case class VAR(name:String) extends Term {
  override def toString:String = name;
}
//
// module definitions
//
abstract class Binding;
case class BIND(name:String,term:Term) extends Binding;

object parser {

  def parseEntry(s:String):Term = {
    lexer.initWith(s);
    parseTerm();
  }

  def parseModule(f:String):List[Binding] = {
    // open the source file
    println("[opening "+f+"]");
    val source = scala.io.Source.fromFile(f);
    lexer.initWith(source.mkString);
    source.close();
    
    // parse each function definition
    var ds:List[Binding] = Nil;
    while (lexer.nextToken() != EOFt) {
      ds = parseDefn()::ds;
    }
    return ds;
  }

  def parseDefn():Binding = {
    // <defn> ::= <id> := <term>
    val x:String = lexer.consumeNAMEt();
    lexer.consumeToken(ASSIGNt);
    val t:Term = parseTerm();
    lexer.consumeToken(SEMIt);
    BIND(x,t)
  }
  
  def parseTerm():Term = {
    lexer.nextToken() match {
      case SLASHt => {
        lexer.consumeToken(SLASHt);
        val x:String = lexer.consumeNAMEt();
        lexer.consumeToken(DOTt);
        val t:Term = parseTerm();
        LAM(x,t)
      }
      case _ => parseApp()
    }
  }

  def parseApp():Term = {
    parseArgs(parseAtom());
  }

  def parseArgs(e:Term):Term = {
    lexer.nextToken() match {
      case SEMIt => e
      case RPARENt => e
      case EOFt => e
      case _ => parseArgs(APP(e,parseAtom()))
    }
  }

  def parseAtom():Term = {
    lexer.nextToken() match {
      case LPARENt => {
        lexer.consumeToken(LPARENt);
        val t:Term = parseTerm();
        lexer.consumeToken(RPARENt);
        return t;
      }
      case NAMEt(x) => {
        lexer.advanceToken();
        return VAR(x);
      }
      case t => throw new SyntaxError("Unexpected token "+t+".",t.report());
    }
  }
}

