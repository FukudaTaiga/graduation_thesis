package formula.integer

import formula.str._

trait ReturnInteger {
  def toFormula(map: Map[StrV, Int]): String

  def intVs: Set[IntV]

  def strVs: Set[StrV]
}
//Constant
case class IntC(value: Int) extends ReturnInteger {
  override def toFormula(map: Map[StrV, Int]): String = value.toString

  override def intVs: Set[IntV] = Set()

  override def strVs: Set[StrV] = Set()
}
//IntVarianles
case class IntV(name: String) extends ReturnInteger {
  override def toFormula(map: Map[StrV, Int]): String = "intV_" + name

  override def intVs: Set[IntV] = Set(this)

  override def strVs: Set[StrV] = Set()
}

case class Operation(v1: ReturnInteger, v2: ReturnInteger, op: String) extends ReturnInteger {
  override def toFormula(map: Map[StrV, Int]): String = "(" + op + " " + v1.toFormula(map) + " " + v2.toFormula(map) + ")"

  override def intVs: Set[IntV] = v1.intVs ++ v2.intVs

  override def strVs: Set[StrV] = v1.strVs ++ v2.strVs
}

case class StrLen(strV: StrV) extends ReturnInteger {
  override def toFormula(map: Map[StrV, Int]): String = if(map.contains(strV)) "len_" + map(strV) else "len_" + strV.name

  override def intVs: Set[IntV] = Set()

  override def strVs: Set[StrV] = Set(strV)
}
