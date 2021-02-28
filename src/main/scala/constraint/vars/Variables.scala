package constraint.vars

case class FAState(id: Int)
case class SST_State(id: Int, name: String) {
  override def toString: String = "q" + id + "_" + name
}
case class SST_Var(id: Int, name: String) {
  override def toString: String = "x" + id + "_" + name
}
case class StringVariable(id: Int)
case class TransState(id: Int)
