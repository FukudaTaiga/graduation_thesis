package formula.re

trait ReturnRe {
  def chars: Set[Char]
}
//Σ*
case class ReAllchar() extends ReturnRe {
  override def chars: Set[Char] = Set()
}

case class ReConcat(re1: ReturnRe, re2: ReturnRe) extends ReturnRe {
  override def chars: Set[Char] = re1.chars ++ re2.chars
}

case class ReRange(begin: Char, end: Char) extends ReturnRe {
  override def chars: Set[Char] = List.range(begin, (end + 1).toChar).toSet
}

case class ReStar(re: ReturnRe) extends ReturnRe {
  override def chars: Set[Char] = re.chars
}

case class ReUnion(re1: ReturnRe, re2: ReturnRe) extends ReturnRe {
  override def chars: Set[Char] = re1.chars ++ re2.chars
}

case class StrToRe(str: String) extends ReturnRe {
  override def chars: Set[Char] = str.toCharArray.toSet
}
