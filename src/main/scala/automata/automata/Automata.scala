package automata.automata

import expression.regex._
import constraint.vars.FAState

//任意の状態間に少なくとも一つ遷移をもち、開始、終了状態が唯一つ. Generalized NFA
case class GFA[Q,A](
  states: Set[Q],
  transition : Map[(Q, RegExp),Q],
  qs: Q,
  qf: Q
){
  def getReg(p: Q, q: Q): RegExp = {
    transition.filter(t => t._1._1 == p && t._2 == q).map(t => t._1._2).fold(EmptyExp)((l,r) => AltExp(l,r)).rm
  }

  def eliminate(q: Q): GFA[Q,A] = {
    val newStates = states - q

    val regex = {
      for{
        p <- states
        q <- states
      } yield (p, q) -> getReg(p,q)
    }.toMap

    val newTrans = {
      for{
        p <- newStates
        r <- newStates
      } yield {
        if(regex(p,q) == EmptyExp || regex(q,r) == EmptyExp) (p, regex(p,r)) -> r
        else (p, AltExp(regex(p,r), ConcatExp(regex(p,q), ConcatExp(StarExp(regex(q,q)), regex(q,r))))) -> r
      }
    }.toMap

    GFA(newStates, newTrans, qs, qf)
  }

  def toReg(): RegExp = {
    var e: RegExp = EmptyExp
    if(states.size != 2) eliminate((states diff Set(qs,qf)).head).toReg
    else getReg(qs,qf).rm
  }
}

case class DFA[Q, A](
  states: Set[Q],
  transition: Map[(Q,A), Q],
  q0: Q,
  finalStates: Set[Q],
  input: Set[A] = Set[A]()
){
  def getAlphabet(): Set[A] = if(input.isEmpty) transition.keySet.map(k => k._2) else input

  def details(): Unit = {
    println("inputs is sequence of " + getAlphabet)
    println("initial state is " + q0)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- transition.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        println("arrival: " + transition(k))
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  def trans(q: Q, w: List[A]): Q = {
    w match {
      case Nil => q
      case a::w => trans(transition(q,a), w)
    }
  }

  def accept(w: List[A]) = {
    try
    finalStates.contains(trans(q0, w))
    catch {
      case e: NoSuchElementException => false
    }
  }

  def toGFA(): GFA[Int,A] = {
    val qs = 0
    val qf = states.size + 1

    val m = states.zipWithIndex.map(t => t._1 -> (t._2 + 1)).toMap
    val genstates = states.map(q => m(q)) ++ Set(qs,qf)

    val defaultMap = {
      for{
        p <- states
        q <- states
      } yield (m(p), EmptyExp: RegExp) -> m(q)
    }.toMap

    val gentrans = defaultMap ++ transition.collect{ case ((p,a), q) => (m(p), CharExp(a)) -> m(q) } ++
    finalStates.map(q => (m(q), EpsExp) -> qf).toMap + ((qs, EpsExp) -> m(q0))

    GFA(genstates, gentrans, qs, qf)
  }

  def toReg(): RegExp = toGFA.toReg

  def rename(): DFA[FAState, A] = {
    @scala.annotation.tailrec
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => transition.collect{case ((p, a), r) if(p == q) => r})
      if(newSet == set) set
      else reachable(newSet)
    }
    val reach = reachable(Set(q0))
    val rmap = reach.zipWithIndex.map(t => (t._1 -> FAState(t._2))).toMap
    val rstates = states.collect{case q if(reach(q)) => rmap(q)}
    val rtrans = transition.collect{case ((p, a), r) if(reach(p) && reach(r)) => ((rmap(p), a)->rmap(r))}.toMap
    val rq0 = rmap(q0)
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    DFA(rstates, rtrans, rq0, rfinalStates)
  }

  //thisとthatの受理するRegexのintersectionを受理するautomataを合成.
  def intersect[P](d: DFA[P, A]): DFA[(Q, P), A] = {
    type State = (Q, P)
    @scala.annotation.tailrec
    def makeStates(ls: List[State], res0: Set[State], res1: Map[(State,A), State]): (Set[State], Map[(State,A), State]) = {
      ls match{
        case Nil => (res0, res1)
        case s::rs => {
          val newMap = transition.collect{ case ((p1, a), q1) if p1 == s._1 => (s, a) -> (q1, d.transition(s._2, a)) }
          val newStates = newMap.values.toSet diff res0
          makeStates(newStates.toList ++ rs, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val iq0 = (q0, d.q0)
    val (istates, itrans) = makeStates(List(iq0), Set(iq0), Map())
    val ifs = istates.filter(s => finalStates(s._1) && d.finalStates(s._2))

    DFA(istates, itrans, iq0, ifs)
  }

  def trim: DFA[Q, A] = {
    //q間のrelation rulesによって, closureをとる.
    @scala.annotation.tailrec
    def star(s: Set[Q], rules: Map[Q, Set[Q]]): Set[Q] = {
      val newS = s.flatMap(q => rules.withDefaultValue(Set())(q))
      if (newS ++ s == s) s
      else star(newS ++ s, rules)
    }

    //(p,a)->qに対してpと繋がっているtransitionの集合にまとめ. p->Set(pと繋がっているもの)なるMapを返す.
    val next0 = transition.groupBy(_._1._1).map(t => t._1 -> t._2.map(_._2).toSet)
    //q0からいけるやつ.
    val reachedFromQ0 = star(Set(q0), next0)
    //q0から行けて, そこからもどこかにいけるやつ. DFAだから必ず行き先はある.
    val next = next0.filter(t => reachedFromQ0(t._1)).map(t => t._1 -> t._2.filter(q => reachedFromQ0(q))).filterNot(_._2.isEmpty)
    val newF = finalStates.intersect(reachedFromQ0)
    //q0から行けて, finalStatesにたどり着きうるもの.
    val reachToFinal = reachedFromQ0.filterNot(q => star(Set(q), next).intersect(newF).isEmpty)

    DFA(
      states.intersect(reachToFinal),
      transition.filter(r => reachToFinal(r._1._1) && reachToFinal(r._2)),
      q0,
      finalStates.filter(q => reachToFinal(q))
    )
  }
}

case class NFA[Q,A](
  states: Set[Q],
  t: Map[(Q,Option[A]), Set[Q]],          // εをNoneで表現
  q0: Q,
  finalStates: Set[Q],
  input: Set[A] = Set[A]()
){
  val transition = t.withDefaultValue(Set())     // キーに対して値が定義されていないときに空集合を返す
  def getAlphabet(): Set[A] = if(input.isEmpty) transition.keySet.collect{case (q, Some(a)) => a} else input

  def details(): Unit = {
    println("inputs is sequence of " + getAlphabet)
    println("initial state is " + q0)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- transition.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        println("arrivals: ")
        for(s <- transition(k)){
          println(s)
        }
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  def eclosure(aQs: Set[Q]) = {
    var qs = Set[Q]()
    var newQs = aQs
    while (newQs != qs) {
      qs = newQs
      for (q <- qs) newQs = newQs ++ transition((q, None))
    }
    qs
  }

  def transSet(qs: Set[Q], w: List[A]): Set[Q] = {
    w match {
      case Nil => eclosure(qs)
      case a::w => transSet(eclosure(qs).flatMap(q => transition((q,Some(a)))), w)
    }
  }

  def trans(q: Q, w: List[A]): Set[Q] = transSet(Set(q), w)

  def accept(w: List[A]) = !(trans(q0, w) & finalStates).isEmpty

  def toDFA(): DFA[Set[Q],A] = {
    val q0DFA = eclosure(Set(q0))
    type State = Set[Q]
    type Maptype = Map[(State, A), State]
    val alphaset = getAlphabet
    @scala.annotation.tailrec
    def makeStates(list: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      list match{
        case Nil => (res0, res1)
        case qs::rs => {
          val newMap = alphaset.map(a => {
            val qset = transSet(qs, List(a))
            (qs, a) -> qset
          }).toMap
          val newStates = newMap.values.toSet
          val s = (newStates diff res0).toList
          makeStates(rs ++ s, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (statesDFA, transitionDFA) = makeStates(List(q0DFA), Set(q0DFA), Map())
    val finalStatesDFA = statesDFA.filter(qs => !(qs & finalStates).isEmpty)

    DFA(statesDFA, transitionDFA, q0DFA, finalStatesDFA, input)
  }

  def toReg(): RegExp = toDFA.toGFA.toReg

  def rename(): NFA[FAState, A] = {
    @scala.annotation.tailrec
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => transition.collect{case ((p, a), set) if(p == q) => set}.flatten)
      if(newSet == set) set
      else reachable(newSet)
    }
    val reach = reachable(Set(q0))
    val rmap = reach.zipWithIndex.map(t => (t._1 -> FAState(t._2))).toMap
    val rstates = states.collect{case q if(reach(q)) => rmap(q)}
    val rtrans = transition.collect{case ((p, a), set) if(reach(p) && !(reach.intersect(set)).isEmpty) => ((rmap(p), a)->(reach.intersect(set)).map(q => rmap(q)))}.toMap
    val rq0 = rmap(q0)
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    NFA(rstates, rtrans, rq0, rfinalStates)
  }
}

case class NFA2[Q,A](
  states: Set[Q],
  t: Map[(Q,Option[A]),Set[Q]],          // εをNoneで表現
  q0: Set[Q],
  finalStates: Set[Q],
  input: Set[A] = Set[A]()
){
  val transition = t.withDefaultValue(Set())
  def getAlphabet(): Set[A] = if(input.isEmpty) transition.keySet.collect{case (q, Some(a)) => a} else input

  def details(): Unit = {
    println("inputs is sequence of " + getAlphabet)
    println("initial state is " + q0)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- transition.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        println("arrivals: ")
        for(s <- transition(k)){
          println(s)
        }
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  def eclosure(aQs: Set[Q]) = {
    var qs = Set[Q]()
    var newQs = aQs
    while (newQs != qs) {
      qs = newQs
      for (q <- qs) newQs = newQs ++ transition((q, None))
    }
    qs
  }

  def transSet(qs: Set[Q], w: List[A]): Set[Q] = {
    w match {
      case Nil => eclosure(qs)
      case a::rs => transSet(eclosure(qs).flatMap(q => transition((q,Some(a)))),rs)
    }
  }

  def accept(w: List[A]) = !(transSet(q0, w) & finalStates).isEmpty

  def toDFA(): DFA[Set[Q],A] = {
    val q0DFA = eclosure(q0)
    type State = Set[Q]
    type Maptype = Map[(State, A), State]
    val alphaset = getAlphabet
    @scala.annotation.tailrec
    def makeStates(list: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      list match{
        case Nil => (res0, res1)
        case qs::rs => {
          val newMap = alphaset.map(a => {
            val qset = transSet(qs, List(a))
            (qs, a) -> qset
          }).toMap
          val newStates = newMap.values.toSet
          val s = (newStates diff res0).toList
          makeStates(rs ++ s, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (statesDFA, transitionDFA) = makeStates(List(q0DFA), Set(q0DFA), Map())
    val finalStatesDFA = statesDFA.filter(qs => !(qs & finalStates).isEmpty)

    DFA(statesDFA, transitionDFA, q0DFA, finalStatesDFA, input)
  }

  def toReg(): RegExp = toDFA.toGFA.toReg

  def rename(): NFA2[FAState, A] = {
    @scala.annotation.tailrec
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => transition.collect{case ((p, a), set) if(p == q) => set}.flatten)
      if(newSet == set) set
      else reachable(newSet)
    }
    val reach = reachable(q0)
    val rmap = reach.zipWithIndex.map(t => (t._1 -> FAState(t._2))).toMap
    val rstates = states.collect{case q if(reach(q)) => rmap(q)}
    val rtrans = transition.collect{case ((p, a), set) if(reach(p) && !(reach.intersect(set)).isEmpty) => ((rmap(p), a)->(reach.intersect(set)).map(q => rmap(q)))}.toMap
    val rq0 = q0.map(q => rmap(q))
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    NFA2(rstates, rtrans, rq0, rfinalStates, input)
  }
}
