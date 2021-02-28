package builder

import constraint.atomicSL.{AtomicSLCons, Concatenation, SSTConstraint, TransducerConstraint}
import constraint.regular.RegCons
import constraint.wordDisEq._
import constraint.vars.{FAState, SST_State, SST_Var, TransState}
import automata.sst.SST
import automata.sst.composition.Composition
import automata.automata.DFA
import automata.transducer.Transducer
import formula.str.StrV

//split: x0#x1#x2#...の#.
case class SSTBuilder[A](
  atomicSLCons: List[AtomicSLCons],
  regCons: Set[RegCons[A]],
  wordDisEqCons: Set[WordDisEq],
  chars: Set[A],
  split: A,
  nameToIdx: Map[StrV, Int],
  getModel: Boolean,
  getLength: Boolean,
  printOption: Boolean = false
){
  type MySST[B] = SST[SST_State, A, B, SST_Var]
  type Out[B] = Either[SST_Var, B]

  val varNum = nameToIdx.size

  //sstList: used in composition, sst_Int: modified, sst_Char: pre, sat: if trimed sst accept no word, then false
  def output: (List[MySST[A]], MySST[Int], MySST[A], Set[(MySST[A], MySST[A])], Boolean) = {
    val idxToName = nameToIdx.map(t => t._2 -> t._1)

    if (atomicSLCons.isEmpty && regCons.isEmpty){
      val sst_char = getStem(varNum, "sst")
      val sstSet = wordDisEqCons.map(wde => getmOne(wde, Map(), sst_char))
      (List(), null, sst_char, sstSet, true)
    }
    else {
      val sstListOption = constraintsToSSTs(atomicSLCons, regCons)
      if(sstListOption.isEmpty)
      (List(), null, null, Set(), false)
      else{
        val sstList = sstListOption.get
        if(printOption){
          println("SST number: " + sstList.size)
          println("SST List: ")
          sstList.foreach(println)
          println()
        }
        val varDFA = regCons.map(t => t.x -> t.r).toMap
        val (sst_int, sst_char, sstNonEmpty) = composeSSTs(sstList, getModel, getLength)
        val sstSet = wordDisEqCons.map(wde => getmOne(wde, varDFA, sst_char))

        (sstList, sst_int, sst_char, sstSet, sstNonEmpty)
      }
    }
  }

  //SST_State(i, name)でSST_Var(i, name)を記録するSST. x_0#x_1#...x_(num-1)#を出力. (x_numは出力しない.)
  def getStem(num: Int, name: String): MySST[A] = {
    //return a sst with |vars| = num, and |states| = num + 1
    val states = Vector.range(0, num + 1).map(i => SST_State(i, name))
    val vars = Vector.range(0, num).map(i => SST_Var(i, name))
    val q0 = states(0)
    val finalMap = Map(states(num) -> vars.foldLeft(List[Either[SST_Var,A]]()) { (x, y) => x ::: List(Left(y), Right(split)) })

    val delta = Vector.range(0, num).flatMap(i => {
      chars.map(c => {
        (states(i), c) -> Option(states(i))
      }) + ((states(i), split) -> Option(states(i + 1)))
    }).toMap

    val unit = vars.map(x => x -> List(Left(x))).toMap  //x -> x

    val eta = Vector.range(0, num).flatMap(i => {
      chars.map(c => {
        (states(i), c) -> (unit + (vars(i) -> List(Left(vars(i)), Right(c))))
      }) + ((states(i), split) -> unit)
    }).toMap

    SST(states.toSet, vars.toSet, delta.withDefaultValue(None), eta.withDefaultValue(unit), q0, finalMap, chars)
  }

  //numはconstraint x_num = (...) のleftになるのでgetStemで0...num-1までを取得し, (...)によってfinalMapを変える.
  def getOne(relCons: AtomicSLCons, varDFA: Map[Int, DFA[FAState, A]]): MySST[A] = {
    val num = relCons.getLeftIdx
    val name = "sst" + num
    val sst0 = getStem(num, name)

    val sst1 = relCons match {
      case c: Concatenation[A] => {
        val newF = sst0.finalMap.map(t =>
          t._1 -> (
            t._2 :::
            c.list.map(e => {
              if (e.isLeft)
              Left(SST_Var(e.left.get, name))
              else
              Right(e.right.get)
            }) :::
            List(Right(split))
          )
        )
        SST(sst0.states, sst0.variables, sst0.delta, sst0.eta, sst0.q0, newF, chars)
      }
      case t: TransducerConstraint[A] => replace(sst0, SST_State(t.source, name), t.fst)
      case s: SSTConstraint[A] => replace(sst0, SST_State(s.source, name), s.sst)
    }

    sst1
  }

  def getmOne(wdeCons: WordDisEq, varDFA: Map[Int, DFA[FAState, A]], sst: MySST[A]): (MySST[A], MySST[A]) = {
    val num = varNum
    val name = "sst" + num
    val sst0 = getStem(num, name)

    val sst1 = sst0.changeFinalMap(wdeCons.getRightIdx, split)
    val sst2 = sst0.changeFinalMap(wdeCons.getLeftIdx, split)
    val sst3 = compose(sst, sst1)
    val sst4 = compose(sst, sst2)
    (sst4, sst3)
  }

  def getNotArtificialVar(idxToName: Map[Int, StrV]): MySST[A] = {
    val num = varNum
    val name = "sst" + num
    val sst0 = getStem(num, name)
    val newF = sst0.finalMap.map(t => t._1 -> t._2.collect{
      case Left(v) if idxToName(v.id).i == 0 => Left(v)
      case Right(c) => Right(c)
    })
    SST(sst0.states, sst0.variables, sst0.delta, sst0.eta, sst0.q0, newF, chars)
  }

  //x_iをemptyにしてしまうSSTがなければ, constraintをSSTにしたListをOptionに包んで返す.
  def constraintsToSSTs(list: List[AtomicSLCons], set: Set[RegCons[A]]): Option[List[MySST[A]]] = {
    @scala.annotation.tailrec
    def star(relCons: List[AtomicSLCons], varDFA: Map[Int, DFA[FAState, A]], res: List[MySST[A]]): Option[List[MySST[A]]] = {
      relCons match {
        case Nil => if(varDFA.isEmpty) Some(res ::: List(getStem(varNum, "sst"))) else Some(res ::: List(getLast(varNum, varDFA)))
        case x :: rest => {
          val leftId = x.getLeftIdx
          x match {
            case _: Concatenation[A] => {
              val regCons = varDFA.filter(p => p._1 < leftId)
              star(rest, varDFA, res ::: List(getOne(x, regCons).trim)) //star(rest, varDFA.filterNot(p => p._1 < leftId), res ::: List(getOne(x, regCons)))
            }
            case t: TransducerConstraint[A] => {
              val regCons = varDFA.filter(p => p._1 < leftId && p._1 != t.source)
              val fst = if(varDFA.contains(t.source)) addDefault(t.fst).intersect(addDefault(varDFA(t.source))).trim.rename else t.fst.trim.rename
              if(fst.states.isEmpty) None
              else star(rest, varDFA, res ::: List(getOne(TransducerConstraint(t.left, fst, t.source), regCons).trim)) //star(rest, varDFA.filterNot(p => p._1 < leftId), res ::: List(getOne(TransducerConstraint(t.left, fst, t.source), regCons)))
            }
            case s: SSTConstraint[A] => {
              val regCons = varDFA.filter(p => p._1 < leftId && p._1 != s.source)
              val sst = if (varDFA.contains(s.source)) compose(dfaToSST(varDFA(s.source)), s.sst).trim else s.sst.trim
              if (sst.states.isEmpty) None
              else star(rest, varDFA, res ::: List(getOne(SSTConstraint(s.left, sst, s.source), regCons).trim)) //star(rest, varDFA.filterNot(p => p._1 < leftId), res ::: List(getOne(SSTConstraint(s.left, sst, s.source), regCons)))
            }
          }
        }
      }
    }

    //Mapに変換.
    val varDFA = set.map(t => t.x -> t.r).toMap
    star(list, varDFA, Nil)
  }

  //getLength: 修正するか否か.
  def composeSSTs(sstList: List[MySST[A]], getModel: Boolean, getLength: Boolean): (MySST[Int], MySST[A], Boolean) = {
    val list = sstList.dropRight(1)
    val last_char = sstList.last.trim
    if (list.size == 0) {
      if(getLength)
      (renameToInt(last_char), last_char, last_char.states.nonEmpty)
      else
      (null, last_char, last_char.states.nonEmpty)
    }
    else {
      val sst0 = composeSSTs(list)
      if(getLength) {
        val sst_int = compose(sst0, renameToInt(last_char)).trim
        val sst_char = compose(sst0, last_char).trim
        (sst_int, sst_char, sst_int.states.nonEmpty)
      }
      else {
        val sst_char = compose(sst0, last_char)
        (null, sst_char, sst_char.states.nonEmpty)
      }
    }
  }

  //sstListのsstを合成したsst.
  def composeSSTs(sstList: List[MySST[A]]): MySST[A] = {
    sstList.tail.foldLeft(sstList.head.trim){
      (x, y) => {
        compose(x, y).trim
      }
    }
  }

  def dfaToSST(dfa: DFA[FAState, A]): MySST[A] = {
    val toNewStates = dfa.states.map(s => s -> SST_State(s.id, "d")).toMap
    val states = dfa.states.map(toNewStates(_))
    val q0 = toNewStates(dfa.q0)
    val x = SST_Var(0, "d")
    val vars = Set(x)
    val delta = dfa.transition.map(r => (toNewStates(r._1._1), r._1._2) -> Option(toNewStates(r._2)))
    val eta = delta.map(r => r._1 -> Map(x -> List(Left(x), Right(r._1._2))))
    val finalMap = dfa.finalStates.map(q => toNewStates(q) -> List(Left(x))).toMap
    SST(states, vars, delta, eta, q0, finalMap, chars)
  }

  //SSTのx_iを記録するq_iを適切な遷移にreplace
  private def replace(sst: MySST[A], q: SST_State, replacement: DFA[FAState, A]): MySST[A] = {
    def tName(s: FAState) = "t" + s.id

    val v = SST_Var(q.id, q.name)
    val toNewStates = replacement.states.map(x => x -> SST_State(q.id, tName(x))).toMap
    val newStates = sst.states - q ++ replacement.states.map(toNewStates(_))
    val newQ0 = {
      if(q == sst.q0) toNewStates.withDefaultValue(SST_State(0, "t0"))(replacement.q0)
      else sst.q0
    }

    val newDelta = sst.delta.filterNot(r => (r._1._1 == q) || (r._2 == Some(q))) ++
    replacement.transition.map(r => (toNewStates(r._1._1), r._1._2) -> Option(toNewStates(r._2))) ++
    sst.delta.filter(r => r._2 == Some(q) && r._1._2 == split).map(r => r._1 -> Option(toNewStates(replacement.q0))) ++
    replacement.finalStates.map(qf => (toNewStates(qf), split) -> sst.delta(q, split)).toMap

    val unit = sst.variables.map(x => x -> List(Left(x))).toMap

    val newEta = sst.eta.filterNot(r => r._1._1 == q) ++
    replacement.transition.map(r => (toNewStates(r._1._1), r._1._2) -> (unit + (v -> List(Left(v), Right(r._1._2))))) ++
    replacement.finalStates.map(qf => (toNewStates(qf), split) -> unit)

    SST(newStates, sst.variables, newDelta, newEta, newQ0, sst.finalMap, chars)
  }

  private def replace(sst: MySST[A], q: SST_State, replacement: MySST[A]): MySST[A] = {
    def tName(id: Int) = "t" + id

    val from = SST_Var(q.id, q.name)
    val to = SST_Var(sst.variables.size, q.name)
    val toNewStates = replacement.states.map(x => x -> SST_State(q.id, tName(x.id))).toMap
    val toNewVars = replacement.variables.map(x => x -> SST_Var(to.id, tName(x.id))).toMap
    val newStates = sst.states - q ++ replacement.states.map(toNewStates(_))
    val newQ0 = if (sst.q0 == q) toNewStates(replacement.q0) else sst.q0
    val newVars = sst.variables + to ++ replacement.variables.map(toNewVars(_))
    val newF = sst.finalMap.map(t => t._1 ->
      List.range(0, to.id + 1).map(i => SST_Var(i, q.name)).foldLeft(List[Either[SST_Var,A]]()) { (x, y) => x ::: List(Left(y), Right(split)) }
    )

    val newDelta = sst.delta.filterNot(r => r._1._1 == q || r._2 == Some(q)) ++
    replacement.delta.collect{ case ((p,a), Some(r)) => (toNewStates(p), a) -> Option(toNewStates(r)) } ++ //map(r => (toNewStates(r._1._1), r._1._2) -> toNewStates(r._2)) ++
    sst.delta.filter(r => r._2 == Some(q) && r._1._2 == split).map(r => r._1 -> Option(toNewStates(replacement.q0))) ++
    replacement.finalMap.keySet.map(qf => (toNewStates(qf), split) -> sst.delta(q, split))

    val unit = (sst.variables + to).map(x => x -> List(Left(x))).toMap ++
    replacement.variables.map(toNewVars(_)).map(x => x -> List[Either[SST_Var,A]]()).toMap

    val newEta = sst.eta.filterNot(r => r._1._1 == q).map(r => r._1 -> (unit ++ r._2)) ++
    replacement.eta.map(r => (
      toNewStates(r._1._1), r._1._2) -> (
        unit ++
        r._2.map(t => toNewVars(t._1) -> t._2.collect {
          case Left(v) => Left(toNewVars(v))
          case Right(c) => Right(c)
        }) +
        (from -> List(Left(from), Right(r._1._2)))
      )
    ) ++
    replacement.finalMap.map(t =>
      (toNewStates(t._1), split) -> (
        unit + (to -> t._2.collect {
          case Left(v) => Left(toNewVars(v))
          case Right(c) => Right(c)
        })
      )
    )

    SST(newStates, newVars, newDelta, newEta, newQ0, newF, chars)
  }

  private def replace(sst: MySST[A], q: SST_State, replacement: Transducer[TransState, A, List[A]]): MySST[A] = {
    def tName(id: Int) = "t" + id

    val from = SST_Var(q.id, q.name)
    val to = SST_Var(sst.variables.size, q.name)
    val toNewStates = replacement.states.map(x => x -> SST_State(q.id, tName(x.id))).toMap
    val newStates = sst.states - q ++ replacement.states.map(toNewStates(_))
    val newQ0 = if (sst.q0 == q) toNewStates(replacement.q0) else sst.q0
    val newVars = sst.variables + to
    val newF = sst.finalMap.map(t => t._1 ->
      List.range(0, to.id + 1).map(i => SST_Var(i, q.name)).foldLeft(List[Either[SST_Var,A]]()) { (x, y) => x ::: List(Left(y), Right(split)) }
    )

    val newDelta = sst.delta.filterNot(r => r._1._1 == q || r._2 == Some(q)) ++
    replacement.delta.map(r => (toNewStates(r._1._1), r._1._2) -> Option(toNewStates(r._2))) ++
    sst.delta.filter(r => r._2 == Some(q) && r._1._2 == split).map(r => r._1 -> Option(toNewStates(replacement.q0))) ++
    replacement.finalStates.map(qf => (toNewStates(qf), split) -> sst.delta(q, split))

    val unit = newVars.map(x => x -> List(Left(x))).toMap

    val newEta = sst.eta.filterNot(r => r._1._1 == q).map(r => r._1 -> (unit ++ r._2)) ++
    replacement.eta.map(
      r => (
        toNewStates(r._1._1), r._1._2
      ) -> (
        unit + (from -> List(Left(from), Right(r._1._2))) + (to -> (List(Left(to)) ::: r._2.map(Right(_))))
      )
    ) ++
    replacement.finalStates.map(t => (toNewStates(t), split) -> unit)

    SST(newStates, newVars, newDelta, newEta, newQ0, newF, chars)
  }

  //modify SST to translate Transducer which output Parikh image
  private def renameToInt(sst: MySST[A]): MySST[Int] = {
    val newF = sst.finalMap.map(
      t => t._1 ->
      List.range(0, sst.variables.filter(v => v.name.contains("sst")).size).map(i => Left(SST_Var(i, t._1.name)))
    )

    val newEta = sst.eta.map(r =>
      r._1 -> r._2.map(t =>
        t._1 -> t._2.collect {
          case Left(v) => Left(v)
          case Right(_) => Right(t._1.id)
        }
      )
    )
    SST(sst.states, sst.variables, sst.delta, newEta, sst.q0, newF, List.range(0, sst.variables.filter(v => v.name.contains("sst")).size).toSet)
  }

  //listのRegexに合わせて全部修正してく.
  private def replaceAllDFA(sst: MySST[A], list: List[(Int, DFA[FAState, A])], name: String): MySST[A] = {
    list match {
      case x :: rest => replaceAllDFA(replace(sst, SST_State(x._1, name), x._2), rest, name)
      case Nil => sst
    }
  }

  //Regexで修正後のSSTを取得.
  private def getLast(num: Int, varDFA: Map[Int, DFA[FAState, A]]): MySST[A] = {
    val sstName = "sst" + num
    replaceAllDFA(getStem(num, sstName), varDFA.toList, sstName).trim
  }


  private def addDefault(dfa: DFA[FAState, A]): DFA[FAState, A] = {
    val sink = FAState(-1)
    DFA(dfa.states + sink, dfa.transition.withDefaultValue(sink), dfa.q0, dfa.finalStates, chars)
  }

  private def addDefault(trans: Transducer[TransState, A, List[A]]): Transducer[TransState, A, List[A]] = {
    val sink = TransState(-1)

    Transducer(trans.states + sink, trans.delta.withDefaultValue(sink), trans.eta, trans.q0, trans.finalStates, chars, chars.map(a => List(a)))
  }

  def compose[X](sst1: MySST[A], sst2: MySST[X]): MySST[X] = Composition(printOption).compose(sst1, sst2)
}
