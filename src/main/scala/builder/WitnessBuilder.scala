package builder

import constraint.vars.{SST_State, SST_Var, TransState}
import automata.sst.SST
import automata.transducer._
import formula.str.StrV
import others.matrix._
import constraint.vars._
import formula.presburger._

//これが呼ばれる時はsat
case class WitnessBuilder(
  z3output: String,
  nameToIdx: Map[StrV, Int],
  yToDelta: Map[Var, ((TransState, Option[Char]), (TransState, (IntVector, IntVector)))],
  zToQ: Map[Var, TransState],
  sToQ: Map[Var, TransState],
  rToQ: Map[Var, TransState],
  sstNatural: SST[SST_State, Char, Char, SST_Var],
  trans: TupleTransducer[TransState, Char, Int],
  chars: Set[Char],
  split: Char,
  intOnly: Boolean
){
  type Transition = ((TransState, Option[Char]), (TransState, (IntVector, IntVector)))

  val idxToName = nameToIdx.map( t => t._2 -> t._1 ).filter(t => t._2.i == 0)

  def output: String = {
    val z3Witness = parse
    val maps = varToIntMap(z3Witness)
    //(0 to 5).foreach(i => maps(i).foreach(println))
    if(intOnly) {
      val witness0 = maps(5).map(t => toModel(t._1.name, t._2.toString, "Int"))
      "(model\n" + witness0.mkString + ")"
    }
    else if(trans == null) {
      val input = getInputSeq(Set(), Map(), null, null)
      val output = sstNatural.accept(input)._2
      val strMap = getString(output, split)
      val vars = nameToIdx.keySet.filter(strV => strV.i == 0)
      val witness0 = maps(5).map(t => toModel(t._1.name, t._2.toString, "Int"))
      val witness1 = strMap.map(t => toModel(t._1.name, t._2, "String"))
      "(model\n" + witness0.mkString + witness1.mkString + "\n)"
    }
    else {
      val deltaInt = maps(1).filter(t => 0 < t._2).map(t => yToDelta(t._1) -> t._2)
      val s0 = sToQ(maps(4).find(s => s._2 == 1).get._1)
      val rf = rToQ(maps(3).find(r => r._2 == 1).get._1)
      val zQ = maps(2).filter(t => 0 <= t._2).map(t => zToQ(t._1)).toSet

      val input = getInputSeq(zQ, deltaInt, rf, s0)
      val output = sstNatural.accept(input)._2
      val strMap = getString(output, split)
      val vars = nameToIdx.keySet.filter(strV => strV.i == 0)

      val witness0 = maps(5).map(t => toModel(t._1.name, t._2.toString, "Int"))
      val witness1 = strMap.map(t => toModel(t._1.name, t._2, "String"))

      "(model\n" + witness0.mkString + witness1.mkString + "\n)"
    }
  }

  def getv(op: Option[(IntVector, IntVector)]): (IntVector, IntVector) = {
    op match{
      case Some(v) => v
      case None => {
        val vz = new IntVector(chars.size, Vector.tabulate(chars.size)(i => 0))
        val uz = new IntVector(chars.size, Vector.tabulate(chars.size)(i => 0))
        (vz, uz)
      }
    }
  }

  def getString(list: List[Char], split: Char): Map[StrV, String] = {
    def getIthString(list: List[Char], i: Int, res: List[Char], k: Int): (StrV, String) = {
      list match{
        case Nil => (idxToName(i) -> res.mkString)  //実際は仕様的に起こらない.
        case c::rs => {
          if(k == i){
            if(c == split) (idxToName(i) -> res.mkString)
            else getIthString(rs, i, res :+ c, k)
          }
          else{
            if(c == split) getIthString(rs, i, res, k + 1)
            else getIthString(rs, i, res, k)
          }
        }
      }
    }

    idxToName.filter(t => t._2.i == 0).keySet.map(i => getIthString(list, i, Nil, 0)).toMap
  }

  def toModel(name: String, value: String, typ: String) = "  (define-fun " + name + " () " + typ + "\n    " + value + ")\n"

  //各VarとStringのMap
  def parse(): Map[String, Int] = {
    //sat (model (define-fun0 y1 ()2 Int3 0)4 (define-fun, x, (), Int, 0),
    val tokens = z3output.replace(10.toChar.toString, " ").replace(13.toChar.toString, " ").split(" ")
    .filterNot(_.isEmpty).toList.drop(2).dropRight(1)  //sat0 (model1 ... )-0 => ...

    def loop(temp: List[String], map: Map[String, Int]): Map[String, Int] = {
      temp match {
        case Nil => map
        case _ => {
          //(define-fun0 x1 ()2 Int3 (-4 1))5
          if (temp(4).startsWith("(-")) loop(temp.drop(6), map + (temp(1) -> -1))
          else loop(temp.drop(5), map + (temp(1) -> temp(4).dropRight(1).toInt))

        }  //y -> 0になる.
      }
    }

    loop(tokens, Map())
  }

  def varToIntMap(m: Map[String, Int]): Map[Int, Map[Var, Int]] = {
    val x = m.collect{ case (str, i) if str.startsWith("lengthOfx") => Var("stringVariable", str.drop(10).toInt) -> i }
    val y = m.collect{ case (str, i) if str.startsWith("numOfDelta") => Var("numOfDelta", str.drop(11).toInt) -> i }
    val z = m.collect{ case (str, i) if str.startsWith("zUsedInTransq") => Var("zUsedInTransq", str.drop(14).toInt) -> i }
    val r = m.collect{ case (str, i) if str.startsWith("recognizeByq") => Var("recognizeByq", str.drop(13).toInt) -> i }
    val s = m.collect{ case (str, i) if str.startsWith("startWithq") => Var("startWithq", str.drop(11).toInt) -> i }
    val k = m.collect{ case (str, i) if str.startsWith("integerVariable") => Var(str.drop(15).dropRight(3), -1) -> i}
    Map(0 -> x, 1 -> y, 2 -> z, 3 -> r, 4 -> s, 5 -> k)
  }

  def getInputSeq(
    zQ: Set[TransState],
    deltaInt: Map[Transition, Int],
    rf: TransState,
    s0: TransState
  ): List[Char] = {
    def search[Q, X](sst: SST[Q, Char, Char, X]): List[Char] = {
      @scala.annotation.tailrec
      def bfs(queue: List[(Q, List[Char])]): List[Char] = {
        queue match{
          case Nil => Nil
          case x :: rs => {
            val (q, ls) = x
            if(sst.finalMap.contains(q)) ls
            else {
              val next = sst.delta.collect{ case ((p, a), Some(r)) if p == q => (r, ls :+ a) }.toList
              bfs(rs ::: next)
            }
          }
        }
      }

      bfs(List((sst.q0, Nil)))
    }

    def eulerPath(remain: Map[Transition, Int]): List[Char] = {
      @scala.annotation.tailrec
      def getPath(current: TransState, fin: TransState, remain: Map[Transition, Int], path: List[Transition]): (Map[Transition, Int], List[Transition]) = {
        if(current == fin) (remain, path)
        else {
          val useEdge = remain.find(t => t._2 > 0 && t._1._1._1 == current).get._1
          getPath(useEdge._2._1, fin, remain + (useEdge -> (remain(useEdge) - 1)), path :+ useEdge)
        }
      }

      @scala.annotation.tailrec
      def getCycle(current: TransState, fin: TransState, remain: Map[Transition, Int], path: List[Transition], b: Boolean): (Map[Transition, Int], List[Transition]) = {
        if(current == fin && b) (remain, path)
        else {
          val useEdge = remain.find(t => t._2 > 0 && t._1._1._1 == current).get._1
          getCycle(useEdge._2._1, fin, remain + (useEdge -> (remain(useEdge) - 1)), path :+ useEdge, true)
        }
      }

      @scala.annotation.tailrec
      def loop(path: List[Transition], remain: Map[Transition, Int]): List[Transition] = {
        if (remain.values.sum == 0) path
        else {
          val p = path.find(t => !remain.filter(s => s._2 > 0 && s._1._1._1 == t._1._1).isEmpty).get._1._1
          val (remain0, cycle) = getCycle(p, p, remain, Nil, false)
          val (pre, post) = path.span(t => t._1._1 != p)
          loop(pre ++ cycle ++ post, remain0)
        }
      }

      val (remain0, path) = getPath(s0, rf, remain, Nil)
      loop(path, remain0).collect{ case ((_, Some(a)), (_, _)) => a}
    }

    if(s0 == null) search(sstNatural)
    else eulerPath(deltaInt)
  }
}
