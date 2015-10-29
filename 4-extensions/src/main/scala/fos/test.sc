package fos

object test {
  println("Welcome to the Scala worksheet")
  import SimplyTypedExtended._;
  
  List[(String,Type)]().reduceRight[(String,Type)]{
      case ((s1, a1), (s2, a2)) if(s2 == "+")=> TypeSum(a1, a2)
      case ((s1, a1), (s2, a2)) if(s2 == "*")=> TypePair(a1, a2)
    }
}