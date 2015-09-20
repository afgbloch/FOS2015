package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "0", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit
  
  /**
   * Helper function
   * 
   * Removes syntactic sugar such that a numeric literal 'x' is transformed into:
   * 'x' * Succ(0).
   */
  def unSugar(numericLit : Int) : Term = numericLit match {
    case 0 => Zero
    case x => Succ(unSugar(x - 1))
  }
  
  /**
   * Helper function
   * 
   * Returns true if the given term t is 0 or of the form succ ..
   */
  def isANumericValue(t: Term): Boolean = t match {
    case Zero => true
    case Succ(t1) => isANumericValue(t1)
    case _ => false
  }

  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | '0'
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */
  def term: Parser[Term] = 
       "true" ^^^ True |
       "false" ^^^ False |
       "if" ~ term ~ "then" ~ term ~ "else" ~ term ^^
       { case i~condition~t~ifTerm~e~elseTerm => If(condition, ifTerm, elseTerm) } |
       "0" ^^^ Zero |
       "succ" ~ term ^^ { case s~successor => Succ(successor) } |
       "pred" ~ term ^^ { case p~predecessor => Pred(predecessor) } |
       "iszero" ~ term ^^ { case z~zeroTerm => IsZero(zeroTerm) } |
       numericLit ^^ (x => unSugar(x.toInt))
       
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 64): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   *  
   *  The evaluation rules are as follows:
   *  
   *  if true then t1 else t2 → t1
   *  if false then t1 else t2 → t2
   *  isZero zero → true
   *  isZero succ NV → false
   *  pred zero → zero
   *  pred succ NV → NV
   *  
   *  t1 → t1'
   *  ——————————————————————————————————————————————
   *  if t1 then t2 else t3 → if t1' then t2 else t3
   *  
   *  t → t'
   *  ————————————————————
   *  isZero t → isZero t'
   *  
   *  t → t'
   *  ————————————————
   *  pred t → pred t'
   *  
   *  t → t'
   *  ————————————————
   *  succ t → succ t'
   */
  def reduce(t: Term): Term =
    t match {
        case If(True, ifTerm, elseTerm) => ifTerm
        case If(False, ifTerm, elseTerm) => elseTerm
        case IsZero(Zero) => True
        case IsZero(Succ(nv)) if isANumericValue(nv) => False
        case Pred(Zero) => Zero
        case Pred(Succ(nv)) if isANumericValue(nv) => nv
        
        case If(cond, ifTerm, elseTerm) => If(reduce(cond), ifTerm, elseTerm)
        case IsZero(t) => IsZero(reduce(t))
        case Pred(t) => Pred(reduce(t))
        case Succ(t) => Succ(reduce(t))
        
        case _ => throw NoReductionPossible(t)
  }

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   *  
   *  Here is how the big step evaluation rules would look for this language:
   *  
   *   v ⇓ v            (B-VALUE)
   *   
   *   t1 ⇓ true     t2 ⇓ v2
   *   ——————————————————————————  (B-IFTRUE)
   *   if t1 then t2 else t3 ⇓ v2
   *   
   *   t1 ⇓ false     t3 ⇓ v3
   *   ——————————————————————————  (B-IFFALSE)
   *   if t1 then t2 else t3 ⇓ v3
   *   
   *   t1 ⇓ nv1
   *   ——————————————————      (B-SUCC)
   *   succ t1 ⇓ succ nv1
   *   
   *   t1 ⇓ 0
   *   ———————————           (B-PREDZERO)
   *   pred t1 ⇓ 0
   *   
   *   t1 ⇓ succ nv1
   *   —————————————          (B-PREDSUCC)
   *   pred t1 ⇓ nv1
   *   
   *   t1 ⇓ 0
   *   ————————————————        (B-ISZEROZERO)
   *   iszero t1 ⇓ true
   *   
   *   t1 ⇓ succ nv1
   *   —————————————————        (B-ISZEROSUCC)
   *   iszero t1 ⇓ false
   */
  def eval(t: Term): Term = t match {
    case Zero => Zero
    case True => True
    case False => False
    case If(cond, ifTerm, elseTerm) if(eval(cond) == True) => eval(ifTerm)
    case If(cond, ifTerm, elseTerm) if(eval(cond) == False) => eval(elseTerm)
    case Succ(t1) if (isANumericValue(eval(t1))) => Succ(eval(t1))
    case Pred(t1) if (eval(t1) == Zero) => Zero
    case Pred(t1) => eval(t1) match {
      case Succ(nv) if (isANumericValue(nv)) => eval(nv)
      case _ => throw TermIsStuck(t)
    }
    case IsZero(t1) if (eval(t1) == Zero) => True
    case IsZero(t1) => eval(t1) match {
      case Succ(nv) if (isANumericValue(nv)) => False
      case _ => throw TermIsStuck(t)
    }
    case _ => throw TermIsStuck(t)
  }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
