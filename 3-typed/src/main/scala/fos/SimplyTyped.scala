package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** 
   *  Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = functAppParser | AppParser | expr
    
  def functAppParser: Parser[Term] = 
      "fst" ~ Term ^^ { case f~t1 => First(t1) } |
      "snd" ~ Term ^^ { case s~t1 => Second(t1) } 
    
  def AppParser: Parser[Term] = 
    expr ~ rep(functAppParser | expr) ^^ { case t1~t2 => t2.foldLeft(t1)((a1, a2) => App(a1, a2))} 

  def expr: Parser[Term]= 
    v |
    "if" ~ Term ~ "then" ~ Term ~ "else" ~ Term ^^
    { case i~condition~t~ifTerm~e~elseTerm => If(condition, ifTerm, elseTerm) } |
    numericLit ^^ (x => unSugar(x.toInt)) |
    "pred" ~ Term ^^ { case p~predecessor => Pred(predecessor) } |
    "succ" ~ Term ^^ { case s~successor => Succ(successor) } |
    "iszero" ~ Term ^^ { case z~zeroTerm => IsZero(zeroTerm) } |
    ident ^^ {case id => Var(id)} |
    "(" ~ Term ~ ")" ^^ { case p1~t~p2 => t} |
    "let" ~ ident ~ ":" ~ Type ~ "=" ~ Term ~ "in" ~ Term ^^ { case l~i~c~ty~e~t1~in~t2 => App(Abs(i, ty, t2),t1)} |
    "{" ~ Term ~ "," ~ Term ~ "}" ^^ { case  c1~t1~c2~t2~c3 => TermPair(t1,t2)}


  def v : Parser[Term] = 
    "true" ^^^ True() |
    "false" ^^^ False() |
    nv |
    "\\" ~ ident ~ ":" ~ Type ~ "." ~ Term ^^ { case l~id~col~ty~dot~term => Abs(id, ty, term)} |
    "{" ~ v ~ "," ~ v ~ "}" ^^ { case c1~v1~c2~v2~c3 => TermPair(v1, v2)}
    
  def nv : Parser[Term] = 
    "0" ^^^ Zero() |
    "succ" ~ nv ^^ { case s~successor => Succ(successor) }
      
  def Type: Parser[Type] = funParse 
      
  def funParse: Parser[Type] = 
    pairParse ~ "->" ~ Type ^^ { case t1~f~t2 => TypeFun(t1, t2)} |
    pairParse
     
      
  def pairParse: Parser[Type] = 
    T ~ "*" ~ Type ^^ { case t1~m~t2 => TypePair(t1, t2)} |
    T
    
  def T: Parser[Type] =
    "Bool" ^^^ TypeBool |
    "Nat" ^^^ TypeNat |
    "(" ~ Type ~ ")" ^^ { case p1~t~p2 => t} 
      
  /**
   * Helper function
   * 
   * Removes syntactic sugar such that a numeric literal 'x' is transformed into:
   * 'x' * Succ(0).
   */
  def unSugar(numericLit : Int) : Term = numericLit match {
    case 0 => Zero()
    case x => Succ(unSugar(x - 1))
  }
  
  var id = 0;
  def uniqId= {
    id += 1
    id
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  def isAValue(t: Term): Boolean = t match {
    case Abs(_,_, _) => true
    case True() => true
    case False() => true
    case _ => isANumericValue(t)
  }
  
    /**
   * Helper function
   * 
   * Returns true if the given term t is 0 or of the form succ ..
   */
  def isANumericValue(t: Term): Boolean = t match {
    case Zero() => true
    case Succ(t1) => isANumericValue(t1)
    case _ => false
  }
  
  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
      case If(True(), ifTerm, elseTerm) => ifTerm
      case If(False(), ifTerm, elseTerm) => elseTerm
      case IsZero(Zero()) => True()
      case IsZero(Succ(nv)) if isANumericValue(nv) => False()
      case Pred(Zero()) => Zero()
      case Pred(Succ(nv)) if isANumericValue(nv) => nv

      case App(Abs(x, t3, t1), t2) if isAValue(t2) => subst(t1, x, t2)
      
      case If(cond, ifTerm, elseTerm) => If(reduce(cond), ifTerm, elseTerm)
      case IsZero(t1) => IsZero(reduce(t1))
      case Succ(t1) => Succ(reduce(t1))
      case Pred(t1) => Pred(reduce(t1))

      case App(t1, t2) if isAValue(t1) => App(t1, reduce(t2))
      case App(t1, t2) => App(reduce(t1), t2)
      
      case First(TermPair(v1, v2)) => v1
      case Second(TermPair(v1, v2)) => v2
      case First(t1) => First(reduce(t1))
      case Second(t1) => Second(reduce(t1))
      case TermPair(v, t1) if isAValue(v) => TermPair(v, reduce(t1))
      case TermPair(t1, t2) => TermPair(reduce(t1), t2)
    
      case _ => throw NoRuleApplies(t)
  }
  
  
  
  
  def alpha(t: Term): Term = t match {
    case Abs(v, t1, t2) => val newName = v + uniqId; Abs(newName, t1, rename(t2, v, newName))
    case _ => t
  }
  
  def rename(t: Term, o:String, n:String): Term = t match {
    case Abs(v, _, _) if v == o => t
    case Abs(v, t1, t2) => Abs(v, t1, rename(t2, o, n))
    case Var(name) if name == o => Var(n)
    case Var(name) => t
    case App(t1, t2) => App(rename(t1, o, n), rename(t2, o, n))
  }

  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = t match {
    case Var(name) if name == x => s 
    case Var(name) => t
    case Abs(v, _, _) if v == x => t
    case Abs(_, _, _) => alpha(t) match{
      case Abs(v2, t1, t2) => Abs(v2, t1, subst(t2, x, s))
      case _ => throw new InternalError
    }
    case App(t1, t2) => App(subst(t1, x, s),subst(t2, x, s))
  }


  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = t match {
    case True() => TypeBool 
    case False() => TypeBool 
    case Zero() => TypeNat
    case Pred(t1) => 
      if(typeof(ctx, t1) == TypeNat) {TypeNat} else { throw new TypeError(t , "expected TypeNat")}
    case Succ(t1) => 
      if(typeof(ctx, t1) == TypeNat) {TypeNat} else { throw new TypeError(t , "expected TypeNat")}
    case IsZero(t1) => 
      if(typeof(ctx, t1) == TypeNat) {TypeBool} else { throw new TypeError(t , "expected TypeNat")}
    case If(cond, ifTerm, elseTerm) => {
      val tCond = typeof(ctx, cond)
      val tIf = typeof(ctx, ifTerm)
      val tElse = typeof(ctx, elseTerm)

      if(tCond == TypeBool && tIf == tElse) {
        tIf
      } else {
        throw new TypeError(t, "failed if");
      }
    }
    case Var(s) => ctx.find(_._1 == s).getOrElse(throw new TypeError(t , "expected TypeNat"))._2
    
    case Abs(x, typeX, t1) => {
      val ctx2 = (x, typeX) :: ctx
      val type1 = typeof(ctx2, t1)
      TypeFun(typeX, type1)
    }
    
    case App(t1, t2) => {
      val type1 = typeof(ctx, t1)
      val type2 = typeof(ctx, t2)
      type1 match {
        case TypeFun(type11, type12) =>if(type2 == type11) {type12} else {throw new TypeError(t , "failed App 1:" + type11)}
        case _ => throw new TypeError(t , "failed App 2")
      }
    }
    
    case TermPair(t1, t2) => TypePair(typeof(ctx, t1),typeof(ctx, t2))
    
    case First(t1) => typeof(ctx, t1) match {
      case TypePair(type1, _) => type1
      case _ => throw new TypeError(t, "Expected TypePair")   
    }
      
    case Second(t1) => typeof(ctx, t1) match {
      case TypePair(_, type2) => type2
      case _ => throw new TypeError(t, "Expected TypePair")   
    }
    
    case _ => throw new TypeError(t, "Unknown Type")   
  }  
  
  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
