package builder

import constraint.atomicSL.{AtomicSLCons, Concatenation, SSTConstraint, TransducerConstraint}
import constraint.wordDisEq._
import constraint.regular.RegCons
import constraint.vars.FAState
import automata.automata._
import automata.factory.{DFAFactory, SSTFactory, TransducerFactory}
import formula._
import formula.atomic._
import formula.str._
import formula.integer._

//from formula to set of Straight-Line constraint
case class SLConsBuilder(formula: ReturnBoolean){
  type outputType = (List[AtomicSLCons], Set[RegCons[Char]], Set[Char], Set[IntegerEquation], Set[StrLenEquation], Set[WordDisEq], Map[StrV, Int])

  //return a list of conjunctive clauses which are in SL
  def output(): List[outputType] = {
    def loop(res: List[outputType], queue: List[Set[Atomic]]): List[outputType] = {
      queue match {
        case Nil => res
        case x :: xs => {
          val we = x.collect { case a: WordEquation => a }.toList
          val sr = x.collect { case a: StrInRe => a }
          val sle = x.collect{ case a: StrLenEquation => a }
          val wde = x.collect{ case a: SomePosDiff => a }
          val ie = x.collect { case a: IntegerEquation => a }
          val strVs = we.flatMap(e => e.strVs).toSet ++ sr.flatMap(e => e.strVs) ++
          sle.flatMap(e => e.strVs) ++ wde.flatMap(e => e.strVs) ++ ie.flatMap(e => e.strVs)
          val charSet = x.flatMap(a => a.chars)
          val chars = if (charSet.isEmpty) Set('a', 'b') else charSet
          val output = SingleSL(we, sr, ie, sle, wde, strVs, chars).output
          if (output.isEmpty)
          loop(res, xs)
          else
          loop(output.get :: res, xs)
        }
      }
    }

    if (formula == null)
    return List()
    loop(List(), toDNF(formula, 1)._1.toList)
  }

  //ReturnBoolean (|, &, ¬を含む形) -> Atomic (IntegerEq, StrInRe, WordEquation, ...)のSetに. Disjunctive Normal Form?
  //一つのSetには同時に満たしているべきAtomicが入る.
  def toDNF(formula: ReturnBoolean, n: Int): (Set[Set[Atomic]], Int) = {
    formula match {
      case a: WordDisequation => {
        val tempVar = StrV("temporaryVar", n)
        val tempEq = WordEquation(tempVar, a.right)
        val lenEq: Set[Atomic] = Set(StrLenEquation(a.left, tempVar), SomePosDiff(a.left, tempVar), tempEq)
        val lenDisEq: Set[Atomic] = Set(IntegerEquation(StrLen(a.left), StrLen(tempVar), -1), tempEq)
        (Set(lenDisEq, lenEq), n + 1)
      }
      case a: Atomic => (Set(Set(a)), n)
      // | はそのまま足す
      case dis: Disjunction => {
        val (d1, m) = toDNF(dis.p1, n)
        val (d2, l) = toDNF(dis.p2, m)
        (d1 ++ d2, l)
      }
      // & は p1 をset of Set[Atomic]に変形したものと p2を変形したものでそれぞれのSet[Atomic]のどれかを満たしていればいい.
      case con: Conjunction => {
        val (d1, m) = toDNF(con.p1, n)
        val (d2, l) = toDNF(con.p2, m)
        (d1.flatMap(clause1 => d2.map(clause2 => clause1 ++ clause2)), l)
      }
      //そのまま
      case neg: Negation => {
        neg.p match {
          case nDis: Disjunction => toDNF(Conjunction(Negation(nDis.p1), Negation(nDis.p2)), n)
          case nCon: Conjunction => toDNF(Disjunction(Negation(nCon.p1), Negation(nCon.p2)), n)
          case nNeg: Negation => toDNF(nNeg.p, n)
          case a: StrInRe => (Set(Set(StrInRe(a.left, a.right, !a.not))), n) //ここからAtomic
          case a: WordEquation => toDNF(WordDisequation(a.left, a.right), n)
          case a: WordDisequation => (Set(Set(WordEquation(a.left, a.right))), n)
          case a: IntegerEquation => (Set(Set(IntegerEquation(a.left, a.right, -a.op))), n)
        }
      }
    }
  }

  //check whether a conjunctive clause is in SL. 実際にAtomicをConstraintに変換し, SLになっているか確認.
  case class SingleSL(we: List[WordEquation], sr: Set[StrInRe], ie: Set[IntegerEquation], sle: Set[StrLenEquation], wde: Set[SomePosDiff], strVs: Set[StrV], chars: Set[Char]) {
    val tf = TransducerFactory(chars)
    val df = DFAFactory(chars)
    val sf = SSTFactory(chars)
    val we_defined_strVs = we.map(t => t.left).toSet

    def output: Option[outputType] = {
      val strVListOption = checkSL(we)
      // Some(ls)なら出現順にstrVが格納されている.
      val strVList = if (strVListOption.isEmpty) List() else strVListOption.get

      if (strVList.isEmpty && strVs.nonEmpty) {
        //not int SL
        return None
      }

      val nameToIdx0 = strVList.zipWithIndex.toMap
      def defVar(m: Map[StrV, Int], strVs: List[StrV]): Map[StrV, Int] = {
        val a = if(m.isEmpty) 0 else m.values.max + 1
        strVs match{
          case Nil => m
          case x::xs => if(m.getOrElse(x, -1) != -1) defVar(m, xs) else defVar(m + (x -> a), xs)
        }
      }
      val nameToIdx = defVar(nameToIdx0, strVs.toList)

      val tuple = (
        atomicConstraints(we, nameToIdx),
        regularConstraints(sr.filter(p => strVs(p.left)), nameToIdx),
        chars,
        ie,
        sle,
        wordDisEqConstraints(wde, nameToIdx),
        nameToIdx
      )
      (Some(tuple))
    }

    //SLであれば出現順のList.
    def checkSL(equations: List[WordEquation]): Option[List[StrV]] = {
      val inoutDegree = checkRedefined(equations)
      if (inoutDegree.isEmpty)
      None
      else
      checkAC(inoutDegree.get._1, inoutDegree.get._2)
    }

    //None : variable is redefined,  or x=x
    def checkRedefined(p: List[WordEquation]): Option[(Map[StrV, Set[StrV]], Map[StrV, Int])] = {

      def _getDepency(p: List[WordEquation], out: Map[StrV, Set[StrV]], in: Map[StrV, Int], definedVars: Set[StrV]):
      Option[(Map[StrV, Set[StrV]], Map[StrV, Int])] = {
        p match {
          case Nil => Some(out, in)
          case x :: xs => {
            //rightに出てくる変数が全種類入ってる.
            val rightVars = x.right.strVs
            //recursive or redefined
            if(rightVars.contains(x.left) || definedVars.contains(x.left)){
              None
            }
            else{
              // x -> {variables of which definition composes x}
              val newTo: Map[StrV, Set[StrV]] = out ++ rightVars.map(y => y -> (out.withDefaultValue(Set())(y) + x.left)).toMap
              // x -> (the number of variables used in definition of x)
              val newFrom: Map[StrV, Int] = in + (x.left -> (rightVars.size + in.withDefaultValue(0)(x.left)))
              _getDepency(xs, newTo, newFrom, definedVars + x.left)
            }
          }
        }
      }

      _getDepency(p, Map(), Map(), Set())
    }

    //None : not AC
    def checkAC(out: Map[StrV, Set[StrV]], in: Map[StrV, Int]): Option[List[StrV]] = {
      def bfs(res: List[StrV], pos: Int, inDegree: Map[StrV, Int]): Option[List[StrV]] = {
        if(res.size == strVs.size){
          Some(res)
        }
        else if(pos < res.size){
          val v = res(pos)
          val update = out.withDefaultValue(Set())(v).map(x => x -> (inDegree(x) - 1))
          //posが1ずつしか増えず, 積んだ順に参照されるbreadth. 間に未定義なのに使っているvarがあると, そのようなvarは出力に含まれずに終わる.
          //全てのvarがvarを使っていて, slになっていないような時はNone. constraintが無限でないならoutが空なvarがあるので止まる.
          bfs(res ::: update.filter(t => t._2 == 0).map(t => t._1).toList, pos + 1, inDegree ++ update)
        }
        else
        None
      }

      val in0 = strVs.filter(x => in.withDefaultValue(0)(x) == 0)
      val in0_we = in0.intersect(we_defined_strVs)
      val in0_sr = in0 -- in0_we
      bfs(in0_sr.toList ::: in0_we.toList, 0, in)
    }

    def atomicConstraints(equations: List[WordEquation], map: Map[StrV, Int]): List[AtomicSLCons] = {
      val res0 = equations.map(e => convertAtomicConstraint(e, map))
      res0.sortWith((a, b) => a.getLeftIdx() < b.getLeftIdx())
    }

    def convertAtomicConstraint(w: WordEquation, map: Map[StrV, Int]): AtomicSLCons = {
      w.right match {
        case a: StrV => Concatenation[Char](map(w.left), List(Left(map(a))))
        case a: StrConcat => Concatenation[Char](
          map(w.left), a.list.flatMap(
            x => x match {
              case Left(strV) => List(Left(map(strV)))
              case Right(str) => str.toCharArray.map(c => Right(c))
            }
          )
        )
        case a: StrSubstrcount => TransducerConstraint(map(w.left), tf.subString(a.begin, a.begin + a.count), map(a.strV))
        case a: StrSubstr => TransducerConstraint(map(w.left), tf.subString(a.begin), map(a.strV))
        case a: StrReplace => {
          if (a.pattern.length == 1) {
            TransducerConstraint(map(w.left), tf.replaceFirst(a.pattern.charAt(0), a.replacement), map(a.strV))
          }
          else {
            SSTConstraint(map(w.left), sf.replaceFirst(a.pattern, a.replacement), map(a.strV))
          }
        }
        case a: StrReplaceAll => {
          if (a.pattern.length == 1) {
            TransducerConstraint(map(w.left), tf.replaceAll(a.pattern.charAt(0), a.replacement), map(a.strV))
          }
          else {
            SSTConstraint(map(w.left), sf.replaceAll(a.pattern, a.replacement), map(a.strV))
          }
        }
        case a: StrAt => TransducerConstraint(map(w.left), tf.subString(a.idx, a.idx + 1), map(a.strV))
        case a: StrReverse => SSTConstraint(map(w.left), sf.reverse, map(a.strV))
        case a: StrInsert => SSTConstraint(map(w.left), sf.insert(a.index, a.str), map(a.strV))
      }
    }

    def regularConstraints(strInRes: Set[StrInRe], map: Map[StrV, Int]): Set[RegCons[Char]] = {
      //満たしているべきDFAの共通部分を取って行く.
      def loop(res: DFA[FAState, Char], list: List[DFA[FAState, Char]]): DFA[FAState, Char] = {
        list match {
          case Nil => res
          case dfa :: xs => loop(dfaIntersect(res, dfa), xs)
        }
      }

      strInRes.groupBy(strInRe => strInRe.left).map(
        t => {
          val strV = t._1
          //strVが満たしているべきDFAのList
          val DFAs = t._2.map(convertRegular(_)).toList
          RegCons(map(strV), loop(DFAs(0), DFAs.drop(1)))
        }
      ).toSet
    }

    def convertRegular(strInRe: StrInRe): DFA[FAState, Char] = {
      if (strInRe.not)
      df.getComplement(df.getDFA(strInRe.right))
      else
      df.getDFA(strInRe.right)
    }

    def wordDisEqConstraints(equations: Set[SomePosDiff], map: Map[StrV, Int]): Set[WordDisEq] = {
      val res0 = equations.map(p => convertWDEq(p, map))
      res0
    }

    def convertWDEq(p: SomePosDiff, map: Map[StrV, Int]): WordDisEq = {
      val left = map(p.left)
      val right = map(p.right)
      WordDisEq(left, right)
    }
  }

  private def addDefault(dfa: DFA[FAState, Char], sigma: Set[Char]): DFA[FAState, Char] = {
    val sink = FAState(-1)
    val states = dfa.states + sink
    val defaultDelta = states.flatMap(s => sigma.map(c => (s, c) -> sink)).toMap
    val delta = defaultDelta ++ dfa.transition
    DFA(states, delta, dfa.q0, dfa.finalStates)
  }

  private def dfaIntersect(dfa1: DFA[FAState, Char], dfa2: DFA[FAState, Char]): DFA[FAState, Char] = {
    val chars_1 = dfa1.transition.map(r => r._1._2).toSet
    val chars_2 = dfa2.transition.map(r => r._1._2).toSet
    val d1 = addDefault(dfa1, chars_1 ++ chars_2)
    val d2 = addDefault(dfa2, chars_1 ++ chars_2)
    d1.intersect(d2).trim.rename
  }
}
