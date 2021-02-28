package constraint.regular

import constraint.vars.FAState
import automata.automata._

case class RegCons[A](x: Int, r: DFA[FAState, A])
