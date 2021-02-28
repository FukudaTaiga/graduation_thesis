package automata.factory

import constraint.vars.FAState
import automata.automata._
import expression.regex._
import formula.re._

case class DFAFactory(charSet: Set[Char]) {

  def getDFA(regex: String) = regToNFA(parseReg(regex.filterNot(_.isWhitespace))).toDFA.trim.rename

  def getDFA(formula: ReturnRe) = regToNFA(formula).toDFA.trim.rename

  //入力された文字列をregexに変換.
  def parseReg(str: String): RegExp = {
    //assert valid
    def f(str: String, start: Int, endChars: Set[Char]): (RegExp, Int) = {
      var cur: RegExp = EpsExp
      var idx = start
      while(idx < str.length && !endChars(str.charAt(idx))){
        str.charAt(idx) match {
          case '|' => {
            val (rex, nextIdx) = f(str, idx + 1, Set(')', '|'))
            cur = AltExp(cur, rex)
            idx = nextIdx
          }
          case '(' => {
            val (rex, nextIdx) = f(str, idx + 1, Set(')'))
            if ((nextIdx + 1) < str.length && str.charAt(nextIdx + 1) == '*') {
              cur = ConcatExp(cur, StarExp(rex))
              idx = nextIdx + 2
            }
            else {
              cur = ConcatExp(cur, rex)
              idx = nextIdx + 1
            }
          }
          case c if (idx + 1 < str.length && str.charAt(idx + 1) == '*') => {
            cur = ConcatExp(cur, StarExp(CharExp(c)))
            idx = idx + 2
          }
          case c => {
            cur = ConcatExp(cur, CharExp(c))
            idx = idx + 1
          }
        }
      }

      (cur, idx)
    }

    def parseDot(str: String): String = {
      val x = "(" + charSet.mkString("|") + ")"
      str.replace(".", x)
    }

    f(parseDot(str), 0, Set())._1
  }

  def regToNFA(formula: ReturnRe): NFA[S, Char] = {
    formula match {
      case a: StrToRe => unitNFA(a.str)
      case a: ReRange => unitNFA(a.chars)
      case _: ReAllchar => unitNFA(charSet)
      case a: ReUnion => altNFA(regToNFA(a.re1), regToNFA(a.re2))
      case a: ReConcat => conNFA(regToNFA(a.re1), regToNFA(a.re2))
      case a: ReStar => starNFA(regToNFA(a.re))
    }
  }

  def regToNFA(regex: RegExp): NFA[S, Char] = {
    regex match {
      case CharExp(c: Char) => unitNFA(c)
      case AltExp(r1, r2) => altNFA(regToNFA(r1), regToNFA(r2))
      case ConcatExp(r1, r2) => conNFA(regToNFA(r1), regToNFA(r2))
      case StarExp(r) => starNFA(regToNFA(r))
      case EmptyExp => emptyNFA()
      case EpsExp => epsilonNFA()
    }
  }

  def getComplement(dfa: DFA[FAState, Char]): DFA[FAState, Char] = {
    //emptyに当たるstate
    val state = FAState(-1)
    val newStates = dfa.states + state
    val newF = newStates.diff(dfa.finalStates)
    //DFAに対してなので, 未定義のcharではemptyに行くようにする.
    val newDelta = newStates.flatMap(s => {
      charSet.map(c => (s, c) -> state)
    }).toMap ++ dfa.transition
    DFA(newStates, newDelta, dfa.q0, newF, charSet).rename
  }

  def dfaIntersect(dfa1: DFA[FAState, Char], dfa2: DFA[FAState, Char]): DFA[FAState, Char] = {
    val chars_1 = dfa1.getAlphabet
    val chars_2 = dfa2.getAlphabet
    val d1 = addDefault(dfa1, chars_1 ++ chars_2)
    val d2 = addDefault(dfa2, chars_1 ++ chars_2)
    d1.intersect(d2).rename
  }

  def addDefault(dfa: DFA[FAState, Char], sigma: Set[Char]): DFA[FAState, Char] = {
    val sink = FAState(-1)
    val states = dfa.states + sink
    val defaultDelta = states.flatMap(s => sigma.map(c => (s, c) -> sink)).toMap
    val delta = defaultDelta ++ dfa.transition
    DFA(states, delta, dfa.q0, dfa.finalStates, charSet)
  }

  private def unitNFA(c: Char): NFA[S, Char] = {
    val q0 = new S
    val q1 = new S
    NFA(Set(q0, q1), Map((q0, Option(c)) -> Set(q1)), q0, Set(q1), charSet)
  }

  private def unitNFA(str: String): NFA[S, Char] = {
    if (str.length == 0)
    epsilonNFA()
    else if (str.length == 1)
    unitNFA(str.charAt(0))
    else
    conNFA(unitNFA(str.charAt(0)), unitNFA(str.substring(1)))
  }

  private def unitNFA(chars: Set[Char]): NFA[S, Char] = {
    if (chars.isEmpty)
    emptyNFA()
    else if (chars.size == 1)
    unitNFA(chars.head)
    //else altNFA(unitNFA(chars.head), unitNFA(chars.tail))
    else{
      val q0 = new S
      val q1 = new S
      val trans = chars.map(c => (q0, Option(c)) -> Set(q1)).toMap
      NFA(Set(q0, q1), trans, q0, Set(q1), charSet)
    }
  }

  private def emptyNFA(): NFA[S, Char] = {
    val q0 = new S
    NFA(Set(q0), Map(), q0, Set(), charSet)
  }

  private def epsilonNFA(): NFA[S, Char] = {
    val q0 = new S
    val q1 = new S
    NFA(Set(q0, q1), Map((q0, None: Option[Char]) -> Set(q1)), q0, Set(q1), charSet)
  }

  private def altNFA(r1: NFA[S, Char], r2: NFA[S, Char]): NFA[S, Char] = {
    val q0 = new S
    NFA(
      r1.states ++ r2.states + q0,
      r1.transition ++ r2.transition ++ Map((q0, None: Option[Char]) -> Set(r1.q0, r2.q0)),
      q0,
      r1.finalStates ++ r2.finalStates,
      charSet
    )
  }

  private def conNFA(r1: NFA[S, Char], r2: NFA[S, Char]): NFA[S, Char] = {
    NFA(
      r1.states ++ r2.states,
      r1.transition ++ r2.transition ++
      r1.finalStates.map(q => (q, None: Option[Char]) -> (r1.transition.getOrElse((q, None), Set()) + r2.q0)).toMap,
      r1.q0,
      r2.finalStates,
      charSet
    )
  }

  private def starNFA(r: NFA[S, Char]): NFA[S, Char] = {
    NFA(
      r.states,
      r.transition ++
      r.finalStates.map(q => (q, None: Option[Char]) -> (r.transition.getOrElse((q, None: Option[Char]), Set()) + r.q0)).toMap,
      r.q0,
      r.finalStates + r.q0,
      charSet
    )
  }

  class S
}
