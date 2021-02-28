package formula.atomic

import formula.ReturnBoolean
import formula.integer.{IntV, ReturnInteger}
import formula.str.{ReturnString, StrV}
import formula.Disjunction
import formula.integer.StrLen
import formula.re.ReturnRe

trait Atomic extends ReturnBoolean

//left = right | left < right ...etc
case class IntegerEquation(left: ReturnInteger, right: ReturnInteger, op: Int) extends Atomic {
  override def strVs: Set[StrV] = left.strVs ++ right.strVs

  override def intVs: Set[IntV] = left.intVs ++ right.intVs

  override def chars: Set[Char] = Set()

  def toFormula(map: Map[StrV, Int]): String = {
    op match {
      case 1 => "(=" + " " + left.toFormula(map) + " " + right.toFormula(map) + ")"
      case -1 => "(not (=" + " " + left.toFormula(map) + " " + right.toFormula(map) + "))"
      case 2 => "(<" + " " + left.toFormula(map) + " " + right.toFormula(map) + ")"
      case -2 => "(>=" + " " + left.toFormula(map) + " " + right.toFormula(map) + ")"
      case 3 => "(>" + " " + left.toFormula(map) + " " + right.toFormula(map) + ")"
      case -3 => "(<=" + " " + left.toFormula(map) + " " + right.toFormula(map) + ")"
    }
  }
}

//left in R
case class StrInRe(left: StrV, right: ReturnRe, not: Boolean) extends Atomic {
  override def strVs: Set[StrV] = Set(left)

  override def intVs: Set[IntV] = Set()

  override def chars: Set[Char] = right.chars
}

//left = T(...)
case class WordEquation(left: StrV, right: ReturnString) extends Atomic {
  override def strVs: Set[StrV] = right.strVs + left

  override def intVs: Set[IntV] = Set()

  override def chars: Set[Char] = right.chars
}

//
case class WordDisequation(left: StrV, right: ReturnString) extends Atomic { //right: ReturnString
  override def strVs: Set[StrV] = right.strVs + left

  override def intVs: Set[IntV] = Set()

  override def chars: Set[Char] = right.chars
}

case class StrLenEquation(left: StrV, right: StrV) extends Atomic{
  override def strVs: Set[StrV] =  Set(left, right)

  override def intVs: Set[IntV] = Set()

  override def chars: Set[Char] = Set()
}

case class SomePosDiff(left: StrV, right: StrV) extends Atomic { //right: ReturnString
  override def strVs: Set[StrV] = Set(right, left)

  override def intVs: Set[IntV] = Set()

  override def chars: Set[Char] = Set()
}
