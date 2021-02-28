package builder

import formula.integer.{IntV, StrLen}
import formula.str.StrV
import formula.presburger._

case class Z3InputBuilder(
  presburger: List[Presburger],
  getModel: Boolean
){
  def output: String = {
    getDeclare + "\n" + proposition + "(check-sat)" + (if (getModel) "\n (get-model)" else "")
  }

  def variables: Set[Var] = presburger.flatMap(p => p.varSet).toSet
  def getDeclare: String = variables.map(v => "(declare-const " + v.toString  + " Int ) \n").mkString
  def proposition: String = presburger.map(pf => "(assert " + pf.mkz3String + ") \n \n").mkString
}
