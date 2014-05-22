//
// reducer.scala
//
// This code defines an object reducer whose "main" 
// method parses and reduces terms of the lambda 
// calculus.  
//
// Briefly, here is the grammar for those terms
//
// <trm> ::= \ <name> . <trm>
// <trm> ::= <trm> <trm>
// <trm> ::= <name> 
// <trm> ::= ( <trm> )
// <name> ::= <any identifier>
//    
// Thus it only contains function abstraction and 
// application.  The top three grammar productions
// correspond to the abstract syntax term constructors:
//
//   LAM : Id * Term -> Term
//   APP : Term * Term -> Term
//   VAR : Id -> Term
//
// As concrete examples, the terms
//
//   \x.x
//   \f.\a.f(f(f a))
//   \h.(\g.h(g g))(\g.h(g g))
//
// correspond to the combinators for identity, the Church
// numeral 3, and for the fixed point Y.  Their abstract
// syntax terms would be
//
//   LAM("x",VAR("x"))
//   LAM("f",LAM("a",APP(VAR("f"),APP(VAR("f"),APP(VAR("f"),VAR("a")))))
//   LAM("h",APP(LAM("g",APP(VAR("h"),APP(VAR("g"),VAR("g")))),
//               LAM("g",APP(VAR("h"),APP(VAR("g"),VAR("g"))))))
//
// We include functionality for parsing  "Church modules."  These
// are text files that give a series of definitions of named terms
// that can then be used within your entry of terms in the reducer.
// An example Church module might contain the definitions:
//
//   I := \x.x;
//   three := \f.\a.f(f(f a));
//   Y := \h.(\g.h(g g))(\g.h(g g));
// 
// When this project is completed, you will be able to
// execute, for any Church module "test.chu", the command
//
//    scala reducer test.chu
//
// This will load in the definitions of named terms into the 
// reducer program, and then enter a REPL where you enter terms
// to be reduce using normal order evaluation.  You could enter
// the term 
//  
//     reduce > (I I) three I;
//
// and the program will begin applying NOR steps to yield a
// term like
//
//     \x$1234.x$1234
//
// The numbers simply indicate variable names. Sometimes, the
// program will rename variables for clarity. For example,
// the lambda term
//
//     (\x.\y.x y) y
//
// could incorrectly substitute to
//
//     \y.y y
//
// The program automatically recognizes these "bound/free" variable
// errors, and will rename variables to avoid them. That is, the term
// two lines above would reduce like so:
//
//     (\x.\y.x y) y ---> (\x.\y$1.x y$1) y ---> \y$1.y y$1,
//
// maintaining the distinction between the bound y and the free y
// by renaming the bound y as y$1.
//

package mdel.lambdaReducer;
package reducer;
import _root_.mdel.lambdaReducer.lexer._;
import _root_.mdel.lambdaReducer.parser._;
import java.io.File;

object Vars {
   var freshest = 0;
   def fresh(name:String):String = {
     freshest = freshest + 1;
     val base = if (name.contains("$")) {
       name.subSequence(0,name.indexOf('$'))
     } else {
       name
     }
     return base+"$"+freshest;  
   }
}

//
// reducer
//
object reducer {

  // free(y,t):
  //
  // A helper function that determines whether 
  // a certain variable y occurs freely in a
  // term t.
  //
  def free(y:String,t:Term):Boolean = {
    val str = t.toString;
    if (str.contains("\\"+y)) {
      return false;
    } else {
      if ( str.contains(y) ) {
        return true;
      } else {
        return false;
      }
    }
  }
  
  // subst(t,x,a):
  //
  // Returns the term that results from replacing
  // all occurrences of x in t with a. Roughly, we
  // are mapping
  //    
  //      k ----> [x/a] bdy   if k=LAM(a,bdy)
  //              k           else,
  //
  // where k is a subterm of t. The function
  // operates casewise. The cases APP and VAR are
  // simplest -- in the case of APP(left,right),
  // we recursively run subst on the subterms 'left'
  // and 'right'. In the case of VAR(nm), there is no
  // substitution to be made unless nm=x.
  //
  // For t = LAM(frml,bdy), we must first ensure that
  // frml does not occur freely in a. If it does, we
  // replace frml with a fresh variable, and then 
  // rerun subst on the updated replacing t with
  // the updated LAM. Assuming the above does not
  // occur, we define
  //
  //    part = subst(bdy,x,a);
  //    full = LAM(frml,part);
  //
  // Depending upon whether part contains frml, we
  // return either 'full' or 'part'. This last if-else
  // statement protects against certain pathological
  // situations.
  //
  def subst(t:Term,x:String,a:Term):Term = {
    t match {
      case LAM(frml,bdy) => 
        if ( free(frml,a) ) {
          val nt = Vars.fresh(frml);
          subst(LAM(nt,subst(bdy,frml,VAR(nt))),x,a);
        } else {

          // We only replace free variables.
          if (frml == x) {
            return t;
          } else {
            return LAM(frml,subst(bdy,x,a));
          }
        }
      case APP(l,r) => 
        val newl = subst(l,x,a);
        val newr = subst(r,x,a);
        return APP(newl,newr);
      case VAR(nm) => 
        if (nm==x) {
          return a;
        } else {
          return VAR(nm);
        }
    }
  }

  // isReducible(t):
  //
  // Determines whether t has a beta-reducible
  // subterm, something of the form APP(LAM(_,_),_).
  //
  // This is a relatively simple case-by-case 
  // implementation. If we have an element of the
  // form APP(LAM(_,_),_), we return true. Otherwise,
  // we recursively run the function on the component
  // parts of LAM or APP, until we find a term of
  // the form APP(LAM(_,_),_). If this doesn't happen,
  // we return False.
  //
  def isReducible(t:Term):Boolean = {
    t match {
      case APP(LAM(_,_),_)  => true;
      case APP(left,right)  => 
        if ( isReducible(left) ) {
          true;
        } else {
          isReducible(right);
        }
      case LAM(frml,bdy)    => isReducible(bdy);
      case VAR(nm)          => false;
    }
  }

  // normalReduce(t):
  //
  // Returns the term that results from finding the
  // leftmost, outermost reducible subterm of t,
  // and applying a beta-reduction step to that
  // subterm.
  //
  // Like above, this is a simple, case-by-case 
  // implementation. We check each term for reducible
  // subterms, recursively calling normalReduce on 
  // those subterms. This is kind of a wasteful version,
  // as we keep calling "isReducible" even after finding
  // a reducible subterm, though this is not that 
  // big of a deal.
  //
  def normalReduce(t:Term):Term = {
    t match {
      case VAR(nm) => return t;
      case LAM(frml,bdy) => 
        if ( isReducible(bdy) ) {
          return LAM(frml,normalReduce(bdy));
        } else {
          return t;
        }
      case APP(LAM(frml,bdy),right) => 
        return subst(bdy,frml,right);
      case APP(left,right) =>
        if ( isReducible(left) ) {
          return APP(normalReduce(left),right);
        } else if ( isReducible(right) ) {
          return APP(left,normalReduce(right))
        } else {
          return t;
        }
      
    }
  }

  //
  // SUPPORTING CODE that uses the above
  //
  def normalize(t:Term,verbose:Boolean):Term = {
    var term:Term = t;
    while(isReducible(term)) {
       if (verbose) println(term);
       term = normalReduce(term);
    } 
    term
  }

  def wrap(defs:List[Binding],term:Term):Term = {
    defs match {
      case Nil => term;
      case BIND(x,t)::bs => wrap(bs,APP(LAM(x,term),t));
      case _ => term;
    }
  }

  def main(args:Array[String]):Unit = {

    // Greet the programmar.
    val classFile:File = new File("reducer.class");
    println("Reed College MATH 384 Church reducer v2014.0 [built: "
	    +new java.util.Date(classFile.lastModified())+"]");

    // Read in the Church module.
    val defs:List[Binding] = if (args.length == 0) {
      Nil
    } else {
      val f:String = args(0);
      try {
	      parser.parseModule(f)
      } catch {
	      case SyntaxError(m,r) => { println(r + m); Nil }
      }
    }

    // Read-eval-print-loop

    // accumulates a series of entered lines
    var entry:String = "";

    // first prompt
    print("reduce > ");

    // first line
    var nextline:String = readLine; 

    while (nextline != null) {

      // read the line(s) that form an expression
      entry = entry + nextline;
      
      if (entry.contains(';')) {
	      // split up the entered text by semicolons
	      val entries = entry.split(';');
	      val hasPartialEntry = if (entry(entry.length-1) == ';') 0 else 1;
	      val numEntries = entries.length-hasPartialEntry; 

	      // process each of the expression entries
	      for (i <- 0 until numEntries) {
	        println(entries(i));
	        val t = parser.parseEntry(entries(i));
	        val it = normalize(wrap(defs,t),true);
	        println(" -*-Bn-> "+ it);
	      }

	      // there might be a partial expression remaining
	      if (hasPartialEntry > 0) {
	        entry = entries(numEntries);
	      } else {
	        entry = "";
	      }
      }

      // output a prompt
      if (entry == "") {
	      print("reduce > ");	
      } else {
	      print(">>>>>>>> ");
      }

      // get the next line
      nextline = readLine;

    }

    println("^D");
  }
}
