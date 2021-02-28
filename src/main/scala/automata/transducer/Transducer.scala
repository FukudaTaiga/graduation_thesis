package automata.transducer

import expression.regex._
import automata.automata._
import others.matrix._
import formula.presburger._
import others.execute._
import constraint.vars.TransState

//deterministic
case class Transducer[Q,A,B](
  states: Set[Q],
  delta: Map[(Q, A), Q],
  eta: Map[(Q, A), B],
  q0: Q,
  finalStates: Set[Q],
  input: Set[A] = Set[A](),
  output: Set[B] = Set[B]()
){
  def getAlphabet = if(input.isEmpty || output.isEmpty) (delta.keySet.map(t => t._2), eta.values.toSet) else (input, output)

  def trans(ls: List[A], q: Q, out: List[B]): (Q, List[B]) = {
    ls match{
      case Nil => (q, out)
      case a::rs => trans(rs, delta(q,a), out ++ List(eta(q,a)))
    }
  }

  def accept(ls: List[A]): (Boolean, List[B]) = {
    val (q, out) = trans(ls, q0, Nil)
    (finalStates(q), out)
  }

  def toBasic(): BaseTransducer[Q,A,B] = {
    val newDelta = delta.map(t => (t._1._1, Option(t._1._2)) -> Set((t._2, eta.get(t._1))))
    BaseTransducer(states, newDelta, q0, finalStates)
  }

  def rename: Transducer[TransState, A, B] = {
    val toNewStates = states.toList.zipWithIndex.map(t => t._1 -> TransState(t._2)).toMap
    Transducer(
      states.map(s => toNewStates(s)),
      delta.map(t => (toNewStates(t._1._1), t._1._2) -> toNewStates(t._2)),
      eta.map(t => (toNewStates(t._1._1), t._1._2) -> t._2),
      toNewStates.withDefaultValue(TransState(0))(q0),
      finalStates.map(s => toNewStates(s))
    )
  }

  def toDFA: DFA[Q, A] = DFA(states, delta, q0, finalStates)

  def trim = {
    val dfa = toDFA.trim
    Transducer(dfa.states, dfa.transition, eta.filter(r => dfa.transition.contains(r._1)), dfa.q0,  dfa.finalStates)
  }

  def intersect[Q1](dfa: DFA[Q1, A]) = {
    val res0: DFA[(Q, Q1), A] = toDFA.intersect(dfa)
    val newEta = res0.transition.map(r => r._1 -> eta(r._1._1._1, r._1._2))
    Transducer(res0.states, res0.transition, newEta, res0.q0, res0.finalStates)
  }
}

//non-deterministic
case class NTransducer[Q,A,B](
  states: Set[Q],
  d: Map[(Q, List[A]), Set[(Q, List[B])]],
  q0: Q,
  finalStates: Set[Q]
){
  val delta = d.withDefaultValue(Set())

  def alphaset = delta.keySet.map(k => k._2)

  def getAlphabet = (delta.keySet.flatMap(k => k._2.toSet), delta.values.flatMap(set => set.flatMap(v => v._2.toSet)).toSet)

  def eclosure(q: Q): Set[Q] = {
    var qs = Set[Q]()
    var nq = Set(q)

    while(qs != nq){
      qs = nq
      for(p <- nq){
        for(t <- delta(p,Nil)) if(t._2.isEmpty) nq += t._1
      }
    }
    qs
  }

  def trans(qs: Set[Q], a: List[A]): Set[(Set[Q], List[B])] = {
    qs.flatMap(q => delta(q,a).map(t => (eclosure(t._1), t._2)))
  }

  def elimEps(): NTransducer[Set[Q],A,B] = {
    //eps遷移を除去
    type State = Set[Q]
    type Maptype = Map[(State, List[A]), Set[(State, List[B])]]
    val eq0 = eclosure(q0)
    val alpha = alphaset
    @scala.annotation.tailrec
    def makeStates(list: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      list match {
        case Nil => (res0, res1)
        case qs::rs => {
          val newMap = alpha.collect{
            case a if a.isEmpty => (qs, a) -> trans(qs,a).filter(t => !(t._2).isEmpty)
            case a => (qs, a) -> trans(qs,a)
          }.toMap
          val newStates = newMap.values.flatten.map(t => t._1).toSet
          val s = (newStates diff res0).toList
          makeStates(rs ++ s, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (estates, edelta) = makeStates(eq0 :: Nil, Set(eq0), Map())

    val efs = estates.filter(qs => !(qs & finalStates).isEmpty)

    NTransducer(estates, edelta, eq0, efs)
  }

  //標準化
  def toBasic(): BaseTransducer[Int,A,B] = {
    //eps遷移を除去
    type Maptype = Map[(Int, Option[A]), Set[(Int, Option[B])]]
    val eq0 = this.elimEps.q0
    val estates = this.elimEps.states
    val edelta = this.elimEps.delta
    val efs = this.elimEps.finalStates
    //遷移をa/eps,eps/bに変換
    var toNewStates = estates.zipWithIndex.toMap

    var bstates = estates.map(qs => toNewStates(qs))
    val bq0 = toNewStates(eq0)
    var bdelta: Maptype = Map().withDefaultValue(Set())
    val bfinalstates = efs.map(qs => toNewStates(qs))

    var bstack = edelta.collect{ case ((qs, as), set) => (toNewStates(qs), as) -> set.map(t => (toNewStates(t._1), t._2)) }

    var check = Map[(Int, List[A]), Set[(Int, List[B])]]()
    var ps = Set[(Int, Option[B])]()
    //入力を書き換える
    while(check != bstack){
      check = bstack
      for(((i, as), set) <- bstack) {
        val k = bstates.max+1
        as match{
          case Nil => {}
          case x :: Nil =>{
            if(set.filter(t => t._2.isEmpty).isEmpty){
              bstack -= ((i,as))
              bdelta += ((i, Option(x)) -> Set((k, None)))
              bstates += k
              bstack += ((k, Nil) -> set)
            }
            else{
              ps = set.filter(t => t._2.isEmpty).map(s => (s._1,None))
              if(set.filter(t => !(t._2.isEmpty)).isEmpty){
                bstack -= ((i,as))
                bdelta += ((i, Option(x)) -> ps)
              }
              else{
                ps += ((k, None))
                bstack -= ((i,as))
                bdelta += ((i, Option(x)) -> ps)
                bstates += k
                bstack += ((k, Nil) -> set.filter(t => !(t._2.isEmpty)))
              }
            }
          }
          case x :: xs => {
            bstack -= ((i,as))
            bdelta += ((i, Option(x)) -> Set((k, None)))
            bstates += k
            bstack += ((k, xs) -> set)
          }
        }
      }
    }

    //出力.この時点でstackにあるのはxs/ys=>eps/ysとなったもの
    while(!bstack.isEmpty){
      for(((i, as), set) <- bstack){
        ps = ps.empty
        for((j, bs) <- set){
          val k = bstates.max+1
          bs match{
            case Nil => {}
            case y :: Nil => {
              ps += ((j, Option(y)))
            }
            case y :: ys => {
              ps += ((k, Option(y)))
              bstates += k
              bstack += ((k, Nil) -> Set((j, ys)))
            }
          }
        }
        bdelta += ((i,None) -> ps)
        bstack -= ((i,as))
      }
    }

    BaseTransducer(bstates, bdelta, bq0, bfinalstates)
  }
}

case class BaseTransducer[Q,A,B](
  states: Set[Q],
  d: Map[(Q, Option[A]),Set[(Q, Option[B])]],
  q0: Q,
  finalStates: Set[Q]
){
  val delta = d.withDefaultValue(Set())

  def domain = {
    val nfa = NFA(states, delta.map(t => (t._1, t._2.map(s => s._1))), q0, finalStates)
    nfa.toDFA.toGFA.toReg
  }

  def getAlphabet(): (Set[A], Set[B]) = {
    val input = delta.keySet.collect{case (q, Some(a)) => a}
    val output = delta.values.flatMap(set => set.collect{case (q, Some(b)) => b}).toSet
    (input, output)
  }

  val eps: Map[(Q,Q), RegExp] = {
    val dtrans = {
      val dset = delta.toSet.filter(t => t._1._2.isEmpty).flatMap(t => t._2.map(s => ((t._1._1, s._2), s._1)))
      (for{
        ((p,b), q) <- dset
      } yield {
        (p,b) -> Set(q)
      }).groupBy(t => t._1).map(t => t._1 -> t._2.foldLeft(Set[Q]())((set, s) => set ++ s._2)).toMap
    }
    states.flatMap(p => states.map(q => ((p, q) -> NFA(states, dtrans, p, Set(q)).toDFA.toGFA.toReg))).toMap
  }

  def details(): Unit = {
    println("inputs is sequence of " + getAlphabet._1)
    println("outputs is sequence of " + getAlphabet._2)
    println("domain is " + domain)
    println("initial state is " + q0)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- delta.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        for(s <- delta(k)){
          println(s)
        }
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  def eclosure(q: Q, r: RegExp): Set[(Q, RegExp)] = {
    val e = states.collect{ case p if eps(q, p) != EmptyExp => (p, ConcatExp(r, eps(q,p)).rm) }
    if(e.filter(x => x._1 == q).isEmpty) e ++ Set((q, r))
    else e
  }

  @scala.annotation.tailrec
  private def transSet(qs: Set[(Q, RegExp)], as: List[A]): Set[(Q, RegExp)] = {
    //(q, r1), (q,r2)を(q, r1|r2)にまとめる
    def grouping(qs: Set[(Q, RegExp)]): Set[(Q, RegExp)] = qs.groupBy(t => t._1).map(t => (t._1, t._2.foldLeft(EmptyExp: RegExp)((regex, r) => AltExp(regex, r._2)).rm)).toSet

    def opToReg(op: Option[B]): RegExp = {
      op match{
        case None => EpsExp
        case Some(b) => CharExp(b)
      }
    }

    as match{
      case Nil => qs
      case a::rs => {
        //aで遷移
        val t1 = qs.flatMap(t => delta(t._1, Option(a)).map(s => (s._1, ConcatExp(t._2, opToReg(s._2)).rm)))
        //eclosure
        val t2 = t1.flatMap(t => eclosure(t._1, t._2))
        transSet(grouping(t2), rs)
      }
    }
  }

  def accept(as: List[A]): (Boolean, RegExp) = {
    val set = transSet(Set((q0, EpsExp)), as).filter(t => finalStates(t._1))
    val regex = set.foldLeft(EmptyExp: RegExp)((reg, t) => AltExp(reg, t._2).rm)
    (!set.isEmpty, regex)
  }

  def rename(): BaseTransducer[TransState, A, B] = {
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => delta.collect{case ((p, a), s) if(p == q) => s.map(t => t._1)}.flatten)
      if(newSet == set){set}
      else{reachable(newSet)}
    }

    val reach = reachable(Set(q0))
    val rmap = reach.zipWithIndex.map(t => (t._1 -> TransState(t._2))).toMap
    val rstates = states.collect{case q if(reach(q)) => rmap(q)}
    val rdelta = delta.collect{case ((p, op), set) if(reach(p) && !(set.filter(t => reach(t._1))).isEmpty) => ((rmap(p), op) -> (set.filter(t => reach(t._1))).map(t => (rmap(t._1), t._2)))}.toMap
    val rq0 = rmap(q0)
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    BaseTransducer(rstates, rdelta, rq0, rfinalStates)
  }

  def trim(): BaseTransducer[Q,A,B] = {
    //q間のrelation rulesによって, closureをとる.
    def star(s: Set[Q], rules: Map[Q, Set[Q]]): Set[Q] = {
      val newS = s.flatMap(q => rules.withDefaultValue(Set())(q))
      if (newS ++ s == s) s
      else star(newS ++ s, rules)
    }

    //(p,a)->qに対してpと繋がっているtransitionの集合にまとめ. p->Set(pと繋がっているもの)なるMapを返す.
    val next0 = delta.groupBy(_._1._1).map(t => t._1 -> t._2.flatMap(s => s._2.map(u => u._1)).toSet)
    //q0からいけるやつ.
    val reachedFromQ0 = star(Set(q0), next0)
    //q0から行けて, そこからもどこかにいけるやつ.
    val next = next0.filter(t => reachedFromQ0(t._1)).map(t => t._1 -> t._2.filter(q => reachedFromQ0(q))).filterNot(_._2.isEmpty)
    val newF = finalStates.intersect(reachedFromQ0)
    //q0から行けて, finalStatesにたどり着きうるもの.
    val reachToFinal = reachedFromQ0.filterNot(q => star(Set(q), next).intersect(newF).isEmpty)

    val newStates = states.intersect(reachToFinal)
    val newDelta = delta.filter(t => reachToFinal(t._1._1)).collect{case ((q, op), set) => (q,op)->set.filter(t => reachToFinal(t._1))}

    new BaseTransducer(newStates, newDelta, q0, newF)
  }

  def comp[P,C](t: BaseTransducer[P,B,C]): BaseTransducer[(Q,P),A,C] = {
    val cq0 = (q0, t.q0)
    type State = (Q,P)
    type Maptype = Map[((Q,P), Option[A]), Set[((Q,P), Option[C])]]
    @scala.annotation.tailrec
    def makeStates(ls: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      ls match{
        case Nil => (res0, res1)
        case x::rs => {
          //a/eps
          val newMap1 = delta.collect{
            case ((q, Some(a)), set) if q == x._1 => {
              val tup = (x, Option(a))
              tup -> (res1.getOrElse(tup, Set()) ++ delta(x._1, Option(a)).map(s => ((s._1, x._2), None: Option[C])))
            }
          }
          //eps/b
          val newMap2 = {
            val tup = (x, None: Option[A])
            Map(
              tup -> (res1.getOrElse(tup, Set()) ++ t.delta(x._2, None).map(s => ((x._1, s._1), s._2)))
            )
          }
          //eps/eps
          val newMap3 = {
            val tup = (x, None: Option[A])
            Map(
              tup -> ((res1 ++ newMap2).getOrElse(tup, Set()) ++ delta(x._1, None).flatMap(s => t.delta(x._2, s._2).map(u => ((s._1, u._1), None: Option[C]))))
            )
          }
          val newMap = newMap1 ++ newMap2 ++ newMap3
          val newStates = newMap.values.flatten.map(t => t._1).toSet
          val s = (newStates diff res0).toList
          makeStates(rs ++ s, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (cstates, cdelta) = makeStates(List(cq0), Set(cq0), Map())

    val cfinalstates = cstates.filter(q => finalStates(q._1) && t.finalStates(q._2))

    BaseTransducer(cstates, cdelta, cq0, cfinalstates)
  }
}

//q0がSetであること以外はBaseTransducerと同じ
case class BaseTransducer2[Q,A,B](
  val states: Set[Q],
  d: Map[(Q, Option[A]),Set[(Q, Option[B])]],
  val q0: Set[Q],
  val finalStates: Set[Q]
){
  val delta = d.withDefaultValue(Set())

  def domain = {
    val nfa = NFA2(states, delta.map(t => (t._1, t._2.map(s => s._1))), q0, finalStates)
    nfa.toDFA.toGFA.toReg
  }

  def getAlphabet(): (Set[A], Set[B]) = {
    val input = delta.keySet.collect{case (q, Some(a)) => a}
    val output = delta.values.flatMap(set => set.collect{case (q, Some(b)) => b}).toSet
    (input, output)
  }

  def details(): Unit = {
    println("inputs is sequence of " + getAlphabet._1)
    println("outputs is sequence of " + getAlphabet._2)
    println("initial states are " + q0)
    println("domain is " + domain)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- delta.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        for(s <- delta(k)){
          println(s)
        }
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  @scala.annotation.tailrec
  private def transSet(qs: Set[(Q, RegExp)], as: List[A]): Set[(Q, RegExp)] = {
    //各状態間でepsで遷移するとき書き込まれる正規言語.繊維がない時はEmptyExp.
    val eps: Map[(Q,Q), RegExp] = {
      val dtrans = {
        val dset = delta.toSet.filter(t => t._1._2.isEmpty).flatMap(t => t._2.map(s => ((t._1._1, s._2), s._1)))
        (for{
          ((p,b), q) <- dset
        } yield {
          (p,b) -> Set(q)
        }).groupBy(t => t._1).map(t => t._1 -> t._2.foldLeft(Set[Q]())((set, s) => set ++ s._2)).toMap
      }
      states.flatMap(p => states.map(q => ((p, q) -> NFA(states, dtrans, p, Set(q)).toDFA.toGFA.toReg))).toMap
    }

    def eclosure(q: Q, r: RegExp): Set[(Q, RegExp)] = {
      val e = states.collect{ case p if eps(q, p) != EmptyExp => (p, ConcatExp(r, eps(q,p)).rm) }
      if(e.filter(x => x._1 == q).isEmpty) e ++ Set((q, r))
      else e
    }

    //(q, r1), (q,r2)を(q, r1|r2)にまとめる
    def grouping(qs: Set[(Q, RegExp)]): Set[(Q, RegExp)] = qs.groupBy(t => t._1).map(t => (t._1, t._2.foldLeft(EmptyExp: RegExp)((regex, r) => AltExp(regex, r._2)).rm)).toSet

    def opToReg(op: Option[B]): RegExp = {
      op match{
        case None => EpsExp
        case Some(b) => CharExp(b)
      }
    }

    as match{
      case Nil => qs
      case a::rs => {
        //aで遷移
        val t1 = qs.flatMap(t => delta(t._1, Option(a)).map(s => (s._1, ConcatExp(t._2, opToReg(s._2)).rm)))
        //eclosure
        val t2 = t1.flatMap(t => eclosure(t._1, t._2))
        transSet(grouping(t2), rs)
      }
    }
  }

  def accept(as: List[A]): (Boolean,RegExp) = {
    val set = transSet(q0.map(q => (q,EpsExp)), as).filter(t => finalStates(t._1))
    val regex = set.foldLeft(EmptyExp: RegExp)((reg, t) => AltExp(reg, t._2)).rm
    (!set.isEmpty, regex)
  }

  def rename(): BaseTransducer2[TransState,A,B] = {
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => delta.collect{case ((p, a), s) if(p == q) => s.map(t => t._1)}.flatten)
      if(newSet == set){set}
      else{reachable(newSet)}
    }

    val reach = reachable(q0)
    val rmap = reach.zipWithIndex.map(t => (t._1 -> TransState(t._2))).toMap
    val rstates = states.collect{case q if(reach(q)) => rmap(q)}
    val rdelta = delta.collect{case ((p, op), set) if(reach(p) && !(set.filter(t => reach(t._1))).isEmpty) => ((rmap(p), op) -> (set.filter(t => reach(t._1))).map(t => (rmap(t._1), t._2)))}.toMap
    val rq0 = q0.map(q => rmap(q))
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    BaseTransducer2(rstates, rdelta, rq0, rfinalStates)
  }

  def trim(): BaseTransducer2[Q,A,B] = {
    //q間のrelation rulesによって, closureをとる.
    def star(s: Set[Q], rules: Map[Q, Set[Q]]): Set[Q] = {
      val newS = s.flatMap(q => rules.withDefaultValue(Set())(q))
      if (newS ++ s == s) s
      else star(newS ++ s, rules)
    }

    //(p,a)->qに対してpと繋がっているtransitionの集合にまとめ. p->Set(pと繋がっているもの)なるMapを返す.
    val next0 = delta.groupBy(_._1._1).map(t => t._1 -> t._2.flatMap(s => s._2.map(u => u._1)).toSet)
    //q0からいけるやつ.
    val reachedFromQ0 = star(q0, next0)
    //q0から行けて, そこからもどこかにいけるやつ.
    val next = next0.filter(t => reachedFromQ0(t._1)).map(t => t._1 -> t._2.filter(q => reachedFromQ0(q))).filterNot(_._2.isEmpty)
    val newF = finalStates.intersect(reachedFromQ0)
    //q0から行けて, finalStatesにたどり着きうるもの.
    val reachToFinal = reachedFromQ0.filterNot(q => star(Set(q), next).intersect(newF).isEmpty)

    val newStates = states.intersect(reachToFinal)
    val newDelta = delta.filter(t => reachToFinal(t._1._1)).collect{case ((q, op), set) => (q,op)->set.filter(t => reachToFinal(t._1))}
    val newQ0 = q0.intersect(reachToFinal)

    new BaseTransducer2(newStates, newDelta, newQ0, newF)
  }

  def comp[P,C](t: BaseTransducer2[P,B,C]): BaseTransducer2[(Q,P),A,C] = {
    val cq0 = q0.flatMap(q => t.q0.map(p => (q,p)))
    type State = (Q,P)
    type Maptype = Map[((Q,P), Option[A]), Set[((Q,P), Option[C])]]
    @scala.annotation.tailrec
    def makeStates(ls: List[(Q,P)], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      ls match{
        case Nil => (res0, res1)
        case x::rs => {
          //a/eps
          val newMap1 = delta.collect{
            case ((q, Some(a)), set) if (q == x._1) => {
              val tup = (x, Option(a))
              tup -> (res1.getOrElse(tup, Set()) ++ delta(x._1 ,Option(a)).map(s => ((s._1, x._2), None: Option[C])))
            }
          }
          //eps/b
          val newMap2 = {
            val tup = (x, None: Option[A])
            Map(
              tup -> (res1.getOrElse(tup, Set()) ++ t.delta(x._2, None).map(s => ((x._1, s._1), s._2)))
            )
          }
          //eps/eps
          val newMap3 = {
            val tup = (x, None: Option[A])
            Map(
              tup -> ((res1 ++ newMap2).getOrElse(tup, Set()) ++ delta(x._1, None).flatMap(s => t.delta(x._2, s._2).map(u => ((s._1, u._1), None: Option[C]))))
            )
          }
          val newMap = newMap1 ++ newMap2 ++ newMap3
          val newStates = newMap.values.flatten.map(t => t._1).toSet
          val s = (newStates diff res0).toList
          makeStates(rs ++ s, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (cstates, cdelta) = makeStates(cq0.toList, cq0, Map())

    val cfinalstates = cstates.filter(q => finalStates(q._1) && t.finalStates(q._2))

    BaseTransducer2(cstates, cdelta, cq0, cfinalstates)
  }
}

class MxgTransducer[Q,A,B](
  states: Set[Q],
  delta: Map[(Q, Option[A]), Set[(Q, Option[IntVector])]],
  q0: Set[Q],
  finalStates: Set[Q],
  output: Set[B]
) extends BaseTransducer2[Q,A,IntVector](states, delta, q0, finalStates){

  override def details(): Unit = {
    println("inputs is sequence of " + getAlphabet1._1)
    println("outputs is sequence of " + getAlphabet1._2)
    println("initial states are " + q0)
    println("domain is " + domain)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- delta.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        for(s <- delta(k)){
          println(s)
        }
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  def getAlphabet1(): (Set[A], Set[B]) = {
    val input = delta.keySet.collect{case (op, Some(a)) => a}
    (input, output)
  }

  override def rename(): MxgTransducer[TransState,A,B] = {
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => delta.collect{case ((p, a), s) if(p == q) => s.map(t => t._1)}.flatten)
      if(newSet == set){set}
      else{reachable(newSet)}
    }

    val reach = reachable(q0)
    val rmap = reach.zipWithIndex.map(t => (t._1 -> TransState(t._2))).toMap
    val rstates = states.collect{case q if(reach(q)) => rmap(q)}
    val rdelta = delta.collect{case ((p, op), set) if(reach(p) && !(set.filter(t => reach(t._1))).isEmpty) => ((rmap(p), op) -> (set.filter(t => reach(t._1))).map(t => (rmap(t._1), t._2)))}.toMap
    val rq0 = q0.map(q => rmap(q))
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    new MxgTransducer(rstates, rdelta, rq0, rfinalStates, output)
  }

  override def trim(): MxgTransducer[Q,A,B] = {
    //q間のrelation rulesによって, closureをとる.
    def star(s: Set[Q], rules: Map[Q, Set[Q]]): Set[Q] = {
      val newS = s.flatMap(q => rules.withDefaultValue(Set())(q))
      if (newS ++ s == s) s
      else star(newS ++ s, rules)
    }

    //(p,a)->qに対してpと繋がっているtransitionの集合にまとめ. p->Set(pと繋がっているもの)なるMapを返す.
    val next0 = delta.groupBy(_._1._1).map(t => t._1 -> t._2.flatMap(s => s._2.map(u => u._1)).toSet)
    //q0からいけるやつ.
    val reachedFromQ0 = star(q0, next0)
    //q0から行けて, そこからもどこかにいけるやつ.
    val next = next0.filter(t => reachedFromQ0(t._1)).map(t => t._1 -> t._2.filter(q => reachedFromQ0(q))).filterNot(_._2.isEmpty)
    val newF = finalStates.intersect(reachedFromQ0)
    //q0から行けて, finalStatesにたどり着きうるもの.
    val reachToFinal = reachedFromQ0.filterNot(q => star(Set(q), next).intersect(newF).isEmpty)

    val newStates = states.intersect(reachToFinal)
    val newDelta = delta.filter(t => reachToFinal(t._1._1)).collect{case ((q, op), set) => (q,op)->set.filter(t => reachToFinal(t._1))}
    val newQ0 = q0.intersect(reachToFinal)

    new MxgTransducer(newStates, newDelta, newQ0, newF, output)
  }

  def getv(op: Option[Int]): Int = {
    op match{
      case Some(v) => v
      case None => 0
    }
  }

  def getv(op: Option[IntVector]): IntVector = {
    op match{
      case Some(v) => v
      case None => new IntVector(output.size, Vector.tabulate(output.size)(i => 0))
    }
  }

  def translate(): TupleTransducer[Q,A,B] = {
    val newDelta = delta.map(t => t._1 -> t._2.map(s => (s._1, Option((getv(s._2), new IntVector(1, Vector(0)))))))
    new TupleTransducer(states, newDelta, q0, finalStates, output, 1)
  }

  //差を出力する
  def subtract[P](t: MxgTransducer[P,A,B]):
  LengthTransducer[(Q, P), A, B] = {
    //println("subtract")
    type TupleState = (Q, P)

    val subq0 = q0.flatMap(q => t.q0.map(p => (q, p)))
    @scala.annotation.tailrec
    def makeStates(ls: List[TupleState], res0: Set[TupleState], res1: Map[(TupleState, Option[A]), Set[(TupleState, Option[Int])]]):
    (Set[TupleState], Map[(TupleState, Option[A]), Set[(TupleState, Option[Int])]]) = {
      ls match{
        case Nil => (res0, res1)
        case tup::rs => {
          val dep1 = delta.filter(r => r._1._1 == tup._1).groupBy(s => s._1._2)
          val keys = dep1.keySet
          val set1 = dep1.map(r => r._1 -> r._2.values.toSet.flatten)
          val set2 = set1.map(
            r => r._1 -> r._2.flatMap(
              s => t.delta(tup._2, r._1).map(
                u => ((s._1,u._1), Option(getv(s._2).length - getv(u._2).length))
              )
            )
          )
          val newMap = keys.map(k => (tup, k) -> set2(k)).toMap
          val newStates = newMap.values.flatMap(s => s.map(u => u._1)).toSet
          val s = (newStates diff res0).toList
          makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (substates, subdelta) = makeStates(subq0.toList, subq0, Map())

    val subfs = substates.filter(tup => finalStates(tup._1) && t.finalStates(tup._2))

    new LengthTransducer(substates, subdelta, subq0, subfs, output)
  }

  //T_NとsubTransducerの直積.
  def product[P,C](lt: LengthTransducer[P,A,C]): TupleTransducer[(Q,P),A,B] = {
    //println("product1")
    type TupleState = (Q, P)

    val proq0 = q0.flatMap(q => lt.q0.map(p => (q, p)))
    @scala.annotation.tailrec
    def makeStates(ls: List[TupleState], res0: Set[TupleState], res1: Map[(TupleState, Option[A]), Set[(TupleState, Option[(IntVector, IntVector)])]]):
    (Set[TupleState], Map[(TupleState, Option[A]), Set[(TupleState, Option[(IntVector, IntVector)])]]) = {
      ls match{
        case Nil => (res0, res1)
        case tup::rs => {
          val dep1 = delta.filter(r => r._1._1 == tup._1).groupBy(s => s._1._2)
          val keys = dep1.keySet  //alphabet
          val set1 = dep1.map(r => r._1 -> r._2.values.toSet.flatten)
          val set2 = set1.map(
            r => r._1 -> r._2.flatMap(
              s => lt.delta(tup._2, r._1).map(
                u => ((s._1, u._1), Option((getv(s._2), new IntVector(1, Vector(getv(u._2))))))
              )
            )
          )
          val newMap = keys.map(k => (tup, k) -> set2(k)).toMap
          val newStates = newMap.values.flatMap(s => s.map(u => u._1)).toSet
          val s = (newStates diff res0).toList
          makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (prostates, prodelta) = makeStates(proq0.toList, proq0, Map())

    val profs = prostates.filter(tup => finalStates(tup._1) && lt.finalStates(tup._2))

    new TupleTransducer(prostates, prodelta, proq0, profs, output, 1)
  }
}

class LengthTransducer[Q,A,B](
  states: Set[Q],
  delta: Map[(Q, Option[A]), Set[(Q, Option[Int])]],
  q0: Set[Q],
  finalStates: Set[Q],
  output: Set[B]
) extends BaseTransducer2[Q, A, Int](states, delta, q0, finalStates){

  override def details(): Unit = {
    println("inputs is sequence of " + getAlphabet1._1)
    println("outputs is sequence of " + getAlphabet1._2)
    println("initial states are " + q0)
    println("domain is " + domain)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- delta.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        for(s <- delta(k)){
          println(s)
        }
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  def getAlphabet1(): (Set[A], Set[B]) = {
    val input = delta.keySet.collect{case (op, Some(a)) => a}
    (input, output)
  }

  override def rename(): LengthTransducer[TransState, A, B] = {
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => delta.collect{case ((p, a), s) if(p == q) => s.map(t => t._1)}.flatten)
      if(newSet == set) set
      else reachable(newSet)
    }

    val reach = reachable(q0)
    val rmap = reach.zipWithIndex.map(t => (t._1 -> TransState(t._2))).toMap
    val rstates = states.collect{case q if(reach(q)) => rmap(q)}
    val rdelta = delta.collect{case ((p, op), set) if(reach(p) && !(set.filter(t => reach(t._1))).isEmpty) => ((rmap(p), op) -> (set.filter(t => reach(t._1))).map(t => (rmap(t._1), t._2)))}.toMap
    val rq0 = q0.map(q => rmap(q))
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    new LengthTransducer(rstates, rdelta, rq0, rfinalStates, output)
  }

  override def trim(): LengthTransducer[Q,A,B] = {
    //q間のrelation rulesによって, closureをとる.
    def star(s: Set[Q], rules: Map[Q, Set[Q]]): Set[Q] = {
      val newS = s.flatMap(q => rules.withDefaultValue(Set())(q))
      if (newS ++ s == s) s
      else star(newS ++ s, rules)
    }

    //(p,a)->qに対してpと繋がっているtransitionの集合にまとめ. p->Set(pと繋がっているもの)なるMapを返す.
    val next0 = delta.groupBy(_._1._1).map(t => t._1 -> t._2.flatMap(s => s._2.map(u => u._1)).toSet)
    //q0からいけるやつ.
    val reachedFromQ0 = star(q0, next0)
    //q0から行けて, そこからもどこかにいけるやつ.
    val next = next0.filter(t => reachedFromQ0(t._1)).map(t => t._1 -> t._2.filter(q => reachedFromQ0(q))).filterNot(_._2.isEmpty)
    val newF = finalStates.intersect(reachedFromQ0)
    //q0から行けて, finalStatesにたどり着きうるもの.
    val reachToFinal = reachedFromQ0.filterNot(q => star(Set(q), next).intersect(newF).isEmpty)

    val newStates = states.intersect(reachToFinal)
    val newDelta = delta.filter(t => reachToFinal(t._1._1)).collect{case ((q, op), set) => (q,op)->set.filter(t => reachToFinal(t._1))}
    val newQ0 = q0.intersect(reachToFinal)

    new LengthTransducer(newStates, newDelta, newQ0, newF, output)
  }

  def getv(op: Option[Int]): Int = {
    op match{
      case Some(v) => v
      case None => 0
    }
  }

  def getv(op: Option[IntVector]): IntVector = {
    op match{
      case Some(v) => v
      case None => new IntVector(output.size, Vector.tabulate(output.size)(i => 0))
    }
  }
}

class TupleTransducer[Q,A,B](
  states: Set[Q],
  delta: Map[(Q, Option[A]), Set[(Q, Option[(IntVector, IntVector)])]],
  q0: Set[Q],
  finalStates: Set[Q],
  output: Set[B],
  size: Int
) extends BaseTransducer2[Q, A, (IntVector, IntVector)](states, delta, q0, finalStates){

  override def details(): Unit = {
    println("inputs is sequence of " + getAlphabet1._1)
    println("outputs is sequence of " + getAlphabet1._2)
    println("initial states are " + q0)
    println("domain is " + domain)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- delta.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        for(s <- delta(k)){
          println(s)
        }
      }
      println()
    }
    println()

    println("finalstates are " + finalStates)
  }

  def getAlphabet1(): (Set[A], Set[B]) = {
    val input = delta.keySet.collect{ case (op, Some(a)) => a }
    (input, output)
  }

  override def rename(): TupleTransducer[TransState, A, B] = {
    def reachable(set: Set[Q]): Set[Q] = {
      val newSet = set ++ set.flatMap(q => delta.collect{case ((p, a), s) if(p == q) => s.map(t => t._1)}.flatten)
      if(newSet == set) set
      else reachable(newSet)
    }

    val reach = reachable(q0)
    val rmap = reach.zipWithIndex.map(t => (t._1 -> TransState(t._2))).toMap
    val rstates = states.collect{ case q if(reach(q)) => rmap(q) }
    val rdelta = delta.collect{
      case ((p, op), set) if(reach(p) && !(set.filter(t => reach(t._1))).isEmpty) => ((rmap(p), op) -> (set.filter(t => reach(t._1))).map(t => (rmap(t._1), t._2)))
    }.toMap
    val rq0 = q0.map(q => rmap(q))
    val rfinalStates = finalStates.intersect(reach).map(q => rmap(q))
    new TupleTransducer(rstates, rdelta, rq0, rfinalStates, output, size)
  }

  override def trim(): TupleTransducer[Q,A,B] = {
    //q間のrelation rulesによって, closureをとる.
    def star(s: Set[Q], rules: Map[Q, Set[Q]]): Set[Q] = {
      val newS = s.flatMap(q => rules.withDefaultValue(Set())(q))
      if (newS ++ s == s) s
      else star(newS ++ s, rules)
    }

    //(p,a)->qに対してpと繋がっているtransitionの集合にまとめ. p->Set(pと繋がっているもの)なるMapを返す.
    val next0 = delta.groupBy(_._1._1).map(t => t._1 -> t._2.flatMap(s => s._2.map(u => u._1)).toSet)
    //q0からいけるやつ.
    val reachedFromQ0 = star(q0, next0)
    //q0から行けて, そこからもどこかにいけるやつ.
    val next = next0.filter(t => reachedFromQ0(t._1)).map(t => t._1 -> t._2.filter(q => reachedFromQ0(q))).filterNot(_._2.isEmpty)
    val newF = finalStates.intersect(reachedFromQ0)
    //q0から行けて, finalStatesにたどり着きうるもの.
    val reachToFinal = reachedFromQ0.filterNot(q => star(Set(q), next).intersect(newF).isEmpty)

    val newStates = states.intersect(reachToFinal)
    val newDelta = delta.filter(t => reachToFinal(t._1._1)).collect{case ((q, op), set) => (q,op)->set.filter(t => reachToFinal(t._1))}
    val newQ0 = q0.intersect(reachToFinal)

    new TupleTransducer(newStates, newDelta, newQ0, newF, output, size)
  }

  def getv(op: Option[Int]): Int = {
    op match{
      case Some(v) => v
      case None => 0
    }
  }

  def getv(op: Option[IntVector]): IntVector = {
    op match{
      case Some(v) => v
      case None => new IntVector(output.size, Vector.tabulate(output.size)(i => 0))
    }
  }

  def getv(op: Option[(IntVector, IntVector)]): (IntVector, IntVector) = {
    op match{
      case Some(v) => v
      case None => {
        val vz = new IntVector(output.size, Vector.tabulate(output.size)(i => 0))
        val uz = new IntVector(size, Vector.tabulate(size)(i => 0))
        (vz, uz)
      }
    }
  }

  //T_NとsubTransducerの直積.
  def product[P,C](lt: LengthTransducer[P,A,C]): TupleTransducer[(Q,P),A,B] = {
    //println("product2")
    type TupleState = (Q, P)

    val proq0 = q0.flatMap(q => lt.q0.map(p => (q, p)))
    @scala.annotation.tailrec
    def makeStates(ls: List[TupleState], res0: Set[TupleState], res1: Map[(TupleState, Option[A]), Set[(TupleState, Option[(IntVector, IntVector)])]]):
    (Set[TupleState], Map[(TupleState, Option[A]), Set[(TupleState, Option[(IntVector, IntVector)])]]) = {
      ls match{
        case Nil => (res0, res1)
        case tup::rs => {
          val dep1 = delta.filter(r => r._1._1 == tup._1).groupBy(s => s._1._2)
          val keys = dep1.keySet
          val set1 = dep1.map(r => r._1 -> r._2.values.toSet.flatten)
          val set2 = set1.map(
            r => r._1 -> r._2.flatMap(
              s => lt.delta(tup._2, r._1).map(
                u => ((s._1,u._1), Option((getv(s._2)._1, getv(s._2)._2.concat(getv(u._2)))))
              )
            )
          )
          val newMap = keys.map(k => (tup, k) -> set2(k)).toMap
          val newStates = newMap.values.flatMap(s => s.map(u => u._1)).toSet
          val s = (newStates diff res0).toList
          makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val (prostates, prodelta) = makeStates(proq0.toList, proq0, Map())

    val profs = prostates.filter(tup => finalStates(tup._1) && lt.finalStates(tup._2))

    new TupleTransducer(prostates, prodelta, proq0, profs, output, size + 1)
  }
}

object TransducerExample0{
  val m = Map[(String,List[Int]), Set[(String,List[Int])]](
    ("p",List(1))->Set(("q",List(1))),
    ("p",List(0))->Set(("p",List(0))),
    ("q",List(1))->Set(("q",Nil)),
    ("q",List(0))->Set(("p",List(0)))
  )

  val n = Map[(String,List[Int]),Set[(String,List[Int])]](
    ("p",List(0))->Set(("q",List(0))),
    ("p",List(1))->Set(("p",List(1))),
    ("q",List(0))->Set(("q",Nil)),
    ("q",List(1))->Set(("p",List(1)))
  )

  val states = Set("p","q")
  val alpha = (Set(0,1), Set(0,1))
  val qs = "p"
  val fs = Set("p","q")
  //tは１の列を一つの１に、sは０で同様の動作をするTransducer
  val t = NTransducer(states, m, qs, fs)
  val s = NTransducer(states, n, qs, fs)
  val bt = t.toBasic
  val bs = s.toBasic
  val comp = bt.comp(bs)

  val states1 = Set(0,1)
  val alpha1 = (Set('0', '1'),Set('0','1'))
  val m1 = Map[(Int,Option[Char]), Set[(Int,Option[Char])]](
    (0,Some('0')) -> Set((0,Some('0'))),
    (0,Some('1')) -> Set((0,None)),
    (0,None) -> Set((1,Some('1'))),
    (1,Some('0')) -> Set((1,Some('0'))),
    (1,Some('1')) -> Set((1,None))
  )
  val qs1 = 0
  val fs1 = Set(1)
  //'0'はそのまま、'1'は全て消去した文字列のランダムな位置に1を挿入した文字列を返す
  val bt1 = BaseTransducer(states1, m1, qs1, fs1)
  val bt12 = BaseTransducer2(states1, m1, Set(qs1), fs1)
}

object TransducerExample1{
  val delta = Map(
    (0, Option('a')) -> Set((0, Option('a'))),
    (0, Option('b')) -> Set((0, Option('c'))),
    (0, None: Option[Char]) -> Set((1, None: Option[Char])),
    (1, Option('a')) -> Set((1, Option('a'))),
    (1, Option('b')) -> Set((1, Option('b')))
  )
  val states = Set(0,1,2)
  val alpha = (Set('a', 'b'), Set('a', 'b', 'c'))
  val q0 = 0
  val finalStates = Set(1)

  val trans = BaseTransducer(states, delta, q0, finalStates)
}
