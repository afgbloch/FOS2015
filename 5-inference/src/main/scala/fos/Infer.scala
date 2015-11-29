package fos

import scala.PartialFunction.OrElse

object Infer {
  case class TypeScheme(params: List[TypeVar], tp: Type)
  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  case class TypeError(msg: String) extends Exception(msg)
  
  var id = 0;
  def freshType = {
    id += 1
    "X" + id
  }
  
  def typeCast(tpe : TypeTree) : Type = tpe match {
    case BoolTypeTree() => BoolType
    case NatTypeTree() => NatType
    case FunTypeTree(tpe1, tpe2) => FunType(typeCast(tpe1), typeCast(tpe2))
    case _ => throw new InternalError
  }

  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match {
    case True() => (BoolType, List())
    case False() => (BoolType, List())
    case Zero() => (NatType, List())
    case Pred(t1) => {
      val (tpe, ct) = collect(env, t1)
      (NatType, (tpe, NatType) :: ct)
    }
    case Succ(t1) => {
      val (tpe, ct) = collect(env, t1)
      (NatType, (tpe, NatType) :: ct)
    }
    case IsZero(t1) => {
      val (tpe, ct) = collect(env, t1)
      (BoolType, (tpe, NatType) :: ct)
    }
    case If(t1, t2, t3) => {
      val (tpe1, ct1) = collect(env, t1)
      val (tpe2, ct2) = collect(env, t2)
      val (tpe3, ct3) = collect(env, t3)
      val ct = (tpe1, BoolType) :: (tpe2, tpe3) :: ct1 ::: ct2 ::: ct3
      (tpe2, ct)
    }
    
    case Var(name) => {
      val tpe = env.filter(e => e._1 == name).map(e => e._2).head.tp
      (tpe, List())
    }
    
    case Abs(x, treeTp1, t1) => {
      var lVar : List[TypeVar] = List()
      
      val tpe1 = treeTp1 match {
        case EmptyTypeTree() => val tmpTpe = TypeVar(freshType); lVar = tmpTpe :: lVar; tmpTpe 
        case _ => typeCast(treeTp1)
      }
      
      val env2 = (x, TypeScheme(lVar, tpe1)) :: env
      val (tpe2, ct) = collect(env2, t1)
      (FunType(tpe1, tpe2), ct)
    }
    
    case App(t1, t2) => {
      val (tpe1, ct1) = collect(env, t1)
      val (tpe2, ct2) = collect(env, t2)
      val tpeX = TypeVar(freshType)
      val ct = (tpe1, FunType(tpe2, tpeX)) :: ct1 ::: ct2
      (tpeX, ct)
    }
    
    case Let(x, tp, v, t1) => ???
    case _ => throw new InternalError
  }
  
  
  
  def unify(c: List[Constraint]): Type => Type =  c match {
    case Nil => x => x
    case (tpe1, tpe2)::xs if(tpe1 == tpe2) => unify(xs) 
    case (tpe1@TypeVar(name), tpe2)::xs  if(!appear(tpe1, tpe2)) => {
      def f1: Type => Type = {
        case x if(x == tpe1) => tpe2
        case FunType(x1, x2) => FunType(f1(x1), f1(x2))
        case x => x
      } 
      f1 andThen unify(xs.map(x => (f1(x._1), f1(x._2))))  
    }
    case (tpe1, tpe2@TypeVar(name))::xs  if(!appear(tpe2, tpe1)) => {
      def f1: Type => Type = {
        case x if(x == tpe2) => tpe1
        case FunType(x1, x2) => FunType(f1(x1), f1(x2))
        case x => x
      } 
      f1 andThen unify(xs.map(x => (f1(x._1), f1(x._2))))  
    }
    case (FunType(s1, s2), FunType(t1,t2))::xs  => unify((s1, t1) :: (s2, t2) :: xs)

    case (tpe1, tpe2)::xs => throw new TypeError("Could not unify: " + tpe1 + " with " + tpe2)
  }
  
  def appear(tpe1: Type, tpe2: Type): Boolean = tpe2 match {
    case FunType(tpe21, tpe22) => appear(tpe1, tpe21) || appear(tpe1, tpe22)
    case _ => tpe1 == tpe2
  }
  
}
