package formula.str

trait ReturnString {
  def strVs: Set[StrV]

  def chars: Set[Char]
}

case class StrV(name: String, i: Int = 0) extends ReturnString {
  override def strVs: Set[StrV] = Set(this)

  override def chars: Set[Char] = Set()
}

/**object StrV {
  def apply(name: String) = new StrV(name, 0)
}*/

case class StrConcat(list: List[Either[StrV, String]]) extends ReturnString {
  override def strVs: Set[StrV] = list.collect { case Left(x) => x }.toSet

  override def chars: Set[Char] = list.collect { case Right(str) => str }.flatMap(s => s.toCharArray).toSet
}

case class StrAt(strV: StrV, idx: Int) extends ReturnString {
  override def strVs: Set[StrV] = Set(strV)

  override def chars: Set[Char] = Set()
}

case class StrReverse(strV: StrV) extends ReturnString {
  override def strVs: Set[StrV] = Set(strV)

  override def chars: Set[Char] = Set()
}

case class StrInsert(strV: StrV, index: Int, str: String) extends ReturnString {
  override def strVs: Set[StrV] = Set(strV)

  override def chars: Set[Char] = str.toSet
}

case class StrReplace(strV: StrV, pattern: String, replacement: String) extends ReturnString {
  override def strVs: Set[StrV] = Set(strV)

  override def chars: Set[Char] = pattern.toSet ++ replacement.toSet
}

case class StrReplaceAll(strV: StrV, pattern: String, replacement: String) extends ReturnString {
  override def strVs: Set[StrV] = Set(strV)

  override def chars: Set[Char] = pattern.toSet ++ replacement.toSet
}

case class StrSubstr(strV: StrV, begin: Int) extends ReturnString {
  override def strVs: Set[StrV] = Set(strV)

  override def chars: Set[Char] = Set()
}

case class StrSubstrcount(strV: StrV, begin: Int, count: Int) extends ReturnString {
  override def strVs: Set[StrV] = Set(strV)

  override def chars: Set[Char] = Set()
}
