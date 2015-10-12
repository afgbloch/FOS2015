package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier
  
  var id = 0;
  def uniqId= {
    id += 1
    id
  }
  
  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */
  def term: Parser[Term] =
    expr ~ rep(expr) ^^ { case t1~t2 => t2.foldLeft(t1)((a1, a2) => App(a1, a2))} |
    expr 
   
   def expr =
     ident ^^ {case id => Var(id)} |
     "\\" ~ ident ~ "." ~ term ^^ { case l~id~dot~t => Abs(id, t)} |
    "(" ~ term ~ ")" ^^ { case p1~t~p2 => t}

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  def alpha(t: Term): Term = t match {
    case Abs(v, t1) => val newName = v + uniqId; Abs(newName,rename(t1, v, newName))
    case _=> t
  }
  
  def rename(t: Term, o:String, n:String): Term = t match {
    case Abs(v, _) if v == o => t
    case Abs(_, t1) => rename(t1, o, n)
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
    case Abs(v, t1) if v == x => t
    case Abs(_, _) => alpha(t) match{
      case Abs(v2, t2) => Abs(v2, subst(t2, x, s))
    }
    case App(t1, t2) => App(subst(t1, x, s),subst(t2, x, s))
  }

  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term = t match {
    case Var(name) => t
    case App(Abs(x, t1), t2) => subst(t1, x, t2)
    case Abs(v, t1) => Abs(v, reduceNormalOrder(t1))
    case App(t1, t2) => App(reduceNormalOrder(t1), reduceNormalOrder(t2))
  }

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term =
    ???

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder))
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)

      case e =>
        println(e)
    }
  }
}
