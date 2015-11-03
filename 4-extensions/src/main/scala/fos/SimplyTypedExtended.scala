package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._
import scala.collection.immutable.Nil

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTypedExtended extends  StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
                              "=>", "|")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
                              "case", "of", "inl", "inr", "as")


  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = SimpleTerm

  /** SimpleTerm ::= "true"
   *               | "false"
   *               | number
   *               | "succ" Term
   *               | "pred" Term
   *               | "iszero" Term
   *               | "if" Term "then" Term "else" Term
   *               | ident
   *               | "\" ident ":" Type "." Term
   *               | "(" Term ")"
   *               | "let" ident ":" Type "=" Term "in" Term
   *               | "{" Term "," Term "}"
   *               | "fst" Term
   *               | "snd" Term
   *               | "inl" Term "as" Type
   *               | "inr" Term "as" Type
   *               | "case" Term "of" "inl" ident "=>" Term "|" "inr" ident "=>" Term
   *               | "fix" Term
   *               | "letrec" ident ":" Type "=" Term "in" Term</pre>
   */
  def SimpleTerm: Parser[Term] = functAppParser | AppParser | expr
  
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
    "{" ~ Term ~ "," ~ Term ~ "}" ^^ { case  c1~t1~c2~t2~c3 => TermPair(t1,t2)} |
    "inl" ~ Term ~ "as" ~ Type ^^ { case c1~t1~c2~tpe => Inl(t1, tpe) } |
    "inr" ~ Term ~ "as" ~ Type ^^ { case c1~t1~c2~tpe => Inr(t1, tpe) } |
    "case" ~ Term ~ "of" ~ "inl" ~ ident ~ "=>" ~ Term ~ "|" ~ "inr" ~ ident ~ "=>" ~ Term ^^
      { case c1~t1~c2~c3~i1~c4~t2~c5~c6~i2~c8~t3 => Case(t1, i1, t2, i2, t3)} |
    "fix" ~ Term ^^ { case c1~t1 => Fix(t1)} |
    "letrec" ~ ident ~ ":" ~ Type ~ "=" ~ Term ~ "in" ~ Term ^^
      { case c1~i1~c2~tpe~c3~t1~c4~t2 => App(Abs(i1, tpe, t2), Fix(Abs(i1, tpe, t1)))}


  def v : Parser[Term] = 
    "true" ^^^ True() |
    "false" ^^^ False() |
    nv |
    "\\" ~ ident ~ ":" ~ Type ~ "." ~ Term ^^ { case l~id~col~ty~dot~term => Abs(id, ty, term)} |
    "{" ~ v ~ "," ~ v ~ "}" ^^ { case c1~v1~c2~v2~c3 => TermPair(v1, v2)} |
    "inl" ~ v ~ "as" ~ Type ^^ { case c1~t1~c2~tpe => Inl(t1, tpe) } |
    "inr" ~ v ~ "as" ~ Type ^^ { case c1~t1~c2~tpe => Inr(t1, tpe) } 

    
  def nv : Parser[Term] = 
    "0" ^^^ Zero() |
    "succ" ~ nv ^^ { case s~successor => Succ(successor) }

  /** 
   *  Type       ::= SimpleType [ "->" Type ]
   */
  def Type: Parser[Type] = funParse | SimpleType | BaseType
    
  
  def funParse: Parser[Type] =
    (SimpleType | BaseType)~ "->" ~ Type ^^ { case t1~f~t2 => TypeFun(t1, t2)}

  /** 
   *  SimpleType ::= BaseType [ ("*" SimpleType) | ("+" SimpleType) ]
   */
  def SimpleType: Parser[Type] = 
    BaseType ~ rep("*" ~ BaseType | "+" ~ BaseType) ^^
    {
      case t1 ~ t2 =>
        {
          val e: List[(String, Type)] = (("", t1) :: t2.map { case x => (x._1, x._2) })
          e.reduceRight[(String, Type)] {
            case ((s1, a1), (s2, a2)) if (s2 == "+") => (s1, TypeSum(a1, a2))
            case ((s1, a1), (s2, a2)) if (s2 == "*") => (s1, TypePair(a1, a2))
          }
        }._2
    }
    
  /** 
   *  BaseType ::= "Bool" | "Nat" | "(" Type ")"
   */
  def BaseType: Parser[Type] =
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


  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case If(True(), ifTerm, elseTerm) => ifTerm
    case If(False(), ifTerm, elseTerm) => elseTerm
    case IsZero(Zero()) => True()
    case IsZero(Succ(nv)) if isANumericValue(nv) => False()
    case Pred(Zero()) => Zero()
    case Pred(Succ(nv)) if isANumericValue(nv) => nv

    case App(Abs(x, typ, t1), v2) if isAValue(v2) => subst(t1, x, v2)
      
    case If(cond, ifTerm, elseTerm) => If(reduce(cond), ifTerm, elseTerm)
    case IsZero(t1) => IsZero(reduce(t1))
    case Succ(t1) => Succ(reduce(t1))
    case Pred(t1) => Pred(reduce(t1))

    case App(t1, t2) if isAValue(t1) => App(t1, reduce(t2))
    case App(t1, t2) => App(reduce(t1), t2)
      
    case First(TermPair(v1, v2)) if (isAValue(v1) && isAValue(v2)) => v1
    case Second(TermPair(v1, v2)) if (isAValue(v1) && isAValue(v2)) => v2
    case First(t1) => First(reduce(t1))
    case Second(t1) => Second(reduce(t1))
    case TermPair(v1, t2) if isAValue(v1) => TermPair(v1, reduce(t2))
    case TermPair(t1, t2) => TermPair(reduce(t1), t2)
    
    case Case(Inl(v0, tpe), x1, t1, x2, t2) if isAValue(v0) => subst(t1, x1, v0)
    case Case(Inr(v0, tpe), x1, t1, x2, t2) if isAValue(v0) => subst(t2, x2, v0)
    case Case(t0, x1, t1, x2, t2) => Case(reduce(t0), x1, t1, x2, t2)
    case Inl(t1, tpe) => Inl(reduce(t1), tpe)
    case Inr(t1, tpe) => Inr(reduce(t1), tpe)
    
    case Fix(Abs(x, t1, t2)) => subst(t2, x, t)
    case Fix(t1) => Fix(reduce(t1))
    
    case _ => throw NoRuleApplies(t)
  }
  
  def alpha(t: Term): Term = t match {
    case Abs(v, t1, t2) => val newName = v + uniqId; Abs(newName, t1, rename(t2, v, newName))
    case Case(t0, x1, t1, x2, t2) =>{
      val newName1 = x1 + uniqId 
      val newName2 = x2 + uniqId
      Case(t0, newName1, rename(t1, x1, newName1), newName2, rename(t2, x2, newName2))
    }
    case _ => t
  }
  
  var id = 0;
  def uniqId = {
    id += 1
    id
  }
  
  def rename(t: Term, o:String, n:String): Term = t match {
    case Abs(v, _, _) if v == o => t
    case Abs(v, t1, t2) => Abs(v, t1, rename(t2, o, n))
    case Var(name) if name == o => Var(n)
    case Var(name) => t
    case App(t1, t2) => App(rename(t1, o, n), rename(t2, o, n))
    case First(t1) => First(rename(t1, o, n))
    case Second(t1) => Second(rename(t1, o, n))
    case TermPair(t1, t2) => TermPair(rename(t1, o, n), rename(t2, o, n))
    case IsZero(t1) => IsZero(rename(t1, o, n))
    case Zero() => t
    case True() => t
    case False() => t
    case Succ(t1) => Succ(rename(t1, o, n))
    case Pred(t1) => Pred(rename(t1, o, n))
    case If(cond, t1, t2) => If(rename(cond, o, n), rename(t1, o, n), rename(t2, o, n))
    case Inr(t1, tpe) => Inr(rename(t1, o, n), tpe)
    case Inl(t1, tpe) => Inl(rename(t1, o, n), tpe)
    case Fix(t1) => Fix(rename(t1, o, n))
    case Case(t0, x1, t1, x2, t2) => Case(rename(t0, o, n), x1, rename(t1, o, n), x2, rename(t2, o, n))
    case _ => throw new InternalError
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
    case First(t1) => First(subst(t1, x, s))
    case Second(t1) => Second(subst(t1, x, s))
    case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
    case IsZero(t1) => IsZero(subst(t1, x, s))
    case Zero() => t
    case True() => t
    case False() => t
    case Succ(t1) => Succ(subst(t1, x, s))
    case Pred(t1) => Pred(subst(t1, x, s))
    case If(cond, t1, t2) => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
    case Inl(t1, tpe1) => Inl(subst(t1, x, s), tpe1)
    case Inr(t1, tpe1) => Inr(subst(t1, x, s), tpe1)
    case Case(_, _, _, _, _) => alpha(t) match{
      case Case(t0, x1, t1, x2, t2) => Case(subst(t0, x, s), x1, subst(t1, x, s), x2, subst(t2, x, s))
      case _ => throw new InternalError
    }
    case Fix(t1) => Fix(subst(t1, x, s))
    
    case _ => throw new InternalError
  }
 

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[Pair[String, Type]]
  
  def isAValue(t: Term): Boolean = t match {
    case Abs(_,_,_) => true
    case True() => true
    case False() => true
    case TermPair(x, y) => isAValue(x) && isAValue(y)
    case Inl(v1, t1) => isAValue(v1)
    case Inr(v1, t1) => isAValue(v1)
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
    
    case Pred(t1) => typeof(ctx, t1) match {
      case TypeNat => TypeNat
      case typ@_ => throw new TypeError(t, "[Pred] expected TypeNat but found " + typ)
    }
    
    case Succ(t1) => typeof(ctx, t1) match {
      case TypeNat => TypeNat
      case typ@_ => throw new TypeError(t, "[Succ] expected TypeNat but found " + typ)
    }
    
    case IsZero(t1) => typeof(ctx, t1) match {
      case TypeNat => TypeBool
      case typ@_ => throw new TypeError(t, "[IsZero] expected TypeNat but found " + typ)
    }
    
    case If(cond, ifTerm, elseTerm) => typeof(ctx, cond) match {
      case TypeBool => {
        val tIf = typeof(ctx, ifTerm)
        val tElse = typeof(ctx, elseTerm)
        if (tIf == tElse) {
          return tIf
        } else {
          throw new TypeError(t, "[If-Then-Else] branches have different types: " + tIf + " vs " + tElse)
        }
      }
      case typ@_ => throw new TypeError(t, "[If-Then-Else] expected TypeBool as condition but found " + typ)
    }
    
    case Var(s) => ctx.find(_._1 == s).getOrElse(
        throw new TypeError(t, "[Var] variable " + s + " is not bounded by the current context"))._2
    
    case Abs(x, type1, t) => {
      val ctx2 = (x, type1) :: ctx
      val type2 = typeof(ctx2, t)
      TypeFun(type1, type2)
    }
    
    case App(t1, t2) => {
      val type1 = typeof(ctx, t1)
      val type2 = typeof(ctx, t2)
      type1 match {
        case TypeFun(type11, type12) =>
          if (type2 == type11) {type12}
          else {throw new TypeError(t, "[App] application has conflicting types: " + type2 + " vs " + type11)}
        case typ@_ => throw new TypeError(t, "[App] expected TypeFun as left term type but found " + typ)
      }
    }
    
    case TermPair(t1, t2) => TypePair(typeof(ctx, t1), typeof(ctx, t2))
    
    case First(t1) => typeof(ctx, t1) match {
      case TypePair(type1, _) => type1
      case typ@_ => throw new TypeError(t, "[First] expected TypePair but found " + typ)   
    }
      
    case Second(t1) => typeof(ctx, t1) match {
      case TypePair(_, type2) => type2
      case typ@_ => throw new TypeError(t, "[Second] expected TypePair but found " + typ)   
    }
    
    case Case(t0,x1,t1,x2,t2) => {
      typeof(ctx, t0) match {
        case TypeSum(tpe1, tpe2) => {
          val type1 = typeof((x1, tpe1) :: ctx, t1)
          val type2 = typeof((x2, tpe2) :: ctx, t2)
          if(type1 == type2){
            type1
          } else {
            throw new TypeError(t2, "[Case] invalid TypeSum" + type1 + "!=" + type2)
          }
        }
        case typ@_ => throw new TypeError(t, "[Case] expected TypeSum but found " + typ)   
      }
    }
    
    case Inl(t1, tpe1) => tpe1 match {
      case TypeSum(type1, type2) => {
        val t1Tpe = typeof(ctx, t1)
        if(t1Tpe == type1) {
          tpe1
        } else {
          throw new TypeError(t, "[Inl] expected " + type1 + " but found " + t1Tpe)
        }
      }
      case typ@_ => throw new TypeError(t, "[Inl] expected TypeSum but found " + typ)
    }
    
    case Inr(t1, tpe1) =>  tpe1 match {
      case TypeSum(type1, type2) => {
        val t1Tpe = typeof(ctx, t1)
        if(t1Tpe == type2) {
          tpe1
        } else {
          throw new TypeError(t, "[Inl] expected " + type2 + " but found " + t1Tpe)
        }
      }
      case typ@_ => throw new TypeError(t, "[Inl] expected TypeSum but found " + typ)
    }
    
    case Fix(t1) => typeof(ctx, t1) match {
      case TypeFun(type1, type2) if (type1 == type2) => type1
      case typ@_ => throw new TypeError(t1, "[Inl] expected TypeFun of same type but found " + typ)
    }
    
    case typ@_ => throw new TypeError(t, "Unknown Type => " + typ)   
  }

  def typeof(t: Term): Type = try {
    typeof(Nil, t)
  } catch {
    case err @ TypeError(_, _) =>
      Console.println(err)
      null
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
          println("parsed: " + trees)
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
