package fos

object test {
  println("Welcome to the Scala worksheet")       //> Welcome to the Scala worksheet
  import SimplyTypedExtended._;

  /*val e = List[(String,Type)]().reduceRight[(String,Type)]{
      case ((s1, a1), (s2, a2)) if(s2 == "+")=> (s1,TypeSum(a1, a2))
      case ((s1, a1), (s2, a2)) if(s2 == "*")=> (s1,TypePair(a1, a2))
    }._2*/

  /*BaseType ~ rep("*" ~ BaseType | "+" ~ BaseType) ^^
      { case t1~t2 =>  t2.reduceRight[~[String,Type]]{
      case (~(s1, a1), ~(s2, a2)) if(s2 == "+")=> (s1,TypeSum(a1, a2))
      case (~(s1, a1), ~(s2, a2)) if(s2 == "*")=> (s1,TypePair(a1, a2))
    }  ;???}*/

  /*BaseType ~ rep("*" ~ BaseType | "+" ~ BaseType) ^^
    {
      case t1 ~ t2 =>
        {
          val e: List[(String, Type)] = (("", t1) :: t2.map { case x => (x._1, x._2) })
          e.reduceRight[(String, Type)] {
            case ((s1, a1), (s2, a2)) if (s2 == "+") => (s1, TypeSum(a1, a2))
            case ((s1, a1), (s2, a2)) if (s2 == "*") => (s1, TypePair(a1, a2))
          }
        }._2
    }*/

}