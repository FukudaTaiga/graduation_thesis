package builder

import automata.sst._
import automata.transducer._
import constraint.vars._
import constraint.atomicSL._
import formula.str._
import formula.atomic._
import formula.presburger._
import others.matrix._
import formula.integer._

case class PresburgerBuilder(
  sst: SST[SST_State, Char, Int, SST_Var],
  preTrans: TupleTransducer[TransState, Char, Int],
  ie: Set[IntegerEquation],
  sle: Set[StrLenEquation],
  chars: Set[Char],
  wde: List[(SST[SST_State, Char, Char, SST_Var], SST[SST_State, Char, Char, SST_Var])],
  nameToIdx: Map[StrV, Int],
  charMap: Map[Int, (Set[Char], Boolean)]
){
  val IdxToName = nameToIdx.map(t => t._2 -> t._1)

  def output(): (
    List[Presburger],
    TupleTransducer[TransState, Char, Int],
    Map[Var, ((TransState, Option[Char]), (TransState, (IntVector, IntVector)))],
    Map[Var, TransState],
    Map[Var, TransState],
    Map[Var, TransState]
  ) = {
    if(sst == null) {
      val f = MakeFormula(
        Set[SST_State](),
        Set[((SST_State, Option[Char]),
        (SST_State, (IntVector, IntVector)))](),
        Set[SST_State](),
        Set[SST_State](),
        Set[Int](),
        ie,
        Set[StrLenEquation](),
        true
      )
      (f.output(), null, Map(), Map(), Map(), Map())
    }
    else{
      val trans = parikhTransducer(wde)
      val (f, yToDelta, zToQ, sToQ, rToQ) = makePresburger(trans)
      (f, trans, yToDelta, zToQ, sToQ, rToQ)
    }
  }

  def makePresburger(trans: TupleTransducer[TransState, Char, Int]): (
    List[Presburger],
    Map[Var, ((TransState, Option[Char]), (TransState, (IntVector, IntVector)))],
    Map[Var, TransState],
    Map[Var, TransState],
    Map[Var, TransState]
  ) = {
    def getv(op: Option[(IntVector, IntVector)]): (IntVector, IntVector) = {
      op match{
        case Some(v) => v
        case None => {
          val vz = new IntVector(chars.size, Vector.tabulate(chars.size)(i => 0))
          val uz = new IntVector(wde.size, Vector.tabulate(wde.size)(i => 0))
          (vz, uz)
        }
      }
    }

    val dtup = {
      val set = trans.delta.toSet
      set.flatMap(t => t._2.map(s => (t._1, (s._1, getv(s._2)))))
    }

    val mkF = MakeFormula(trans.states, dtup, trans.q0, trans.finalStates, sst.output, ie, sle, false)
    (mkF.output(), mkF.yToDelta, mkF.zToQ, mkF.sToQ, mkF.rToQ)
  }



  def parikhTransducer(wde: List[(SST[SST_State, Char, Char, SST_Var], SST[SST_State, Char, Char, SST_Var])]):
  TupleTransducer[TransState, Char, Int] = {
    val parikh0 = sst.toParikh
    val parikh = parikh0.trim.rename
    if(wde.isEmpty) parikh.translate.trim.rename
    /**
    else if(preTrans != null) {
      println(wde.size - 1)
      val (sst1, sst2) = wde(wde.size - 1)
      val (s, b) = charMap(wde.size - 1)
      val subset = if(b) s.take(s.size / 2) else s.drop(s.size / 2)
      val other = s diff subset
      val sub = (sst1.toCountSST(subset).toParikh.rename subtract sst2.toCountSST(other).toParikh.rename).trim.rename
      preTrans.product(sub).trim.rename
    }
    */
    else {
      val list1 = wde.zipWithIndex.map(u => {
        val (s, b) = charMap(u._2)
        val subset = if(b) s.take(s.size / 2) else s.drop(s.size / 2)
        val other = s diff subset
        (u._1._1.toCountSST(subset).toParikh.rename subtract u._1._2.toCountSST(other).toParikh.rename).trim.rename
      })
      transducerProduct(parikh, list1)
    }
  }

  def transducerProduct(
    parikh: MxgTransducer[TransState,Char,Int],
    list: List[LengthTransducer[TransState, Char, Char]],
  ):
  TupleTransducer[TransState, Char, Int] = {
    val tup0 = parikh.product(list.head).trim.rename
    list.tail.foldLeft(tup0)((t, l) => t.product(l).trim.rename)
  }

  case class MakeFormula[Q, A](
    states: Set[Q],
    dtup: Set[((Q, Option[A]), (Q, (IntVector, IntVector)))],
    q0: Set[Q],
    finalStates: Set[Q],
    alphabet: Set[Int],
    ie: Set[IntegerEquation],
    sle: Set[StrLenEquation],
    isNull: Boolean
  ) {
    val one: Integers = Const(1)
    val zero: Integers = Const(0)
    val mzero: Integers = Const(- 1)
    //StrVのidとSST_Varのidは共通だから, idから長さを表す変数をとる.
    val xVar = alphabet.map(i => i -> Var("lengthOfx", i)).toMap
    val arrId = alphabet.zipWithIndex.map(t => t._1 -> t._2).toMap
    val yVar = dtup.zipWithIndex.map(t => t._1 -> Var("numOfDelta", t._2)).toMap
    val zVar = states.zipWithIndex.map(t => t._1 -> Var("zUsedInTransq", t._2)).toMap
    val nVar = states.zipWithIndex.map(t => t._1 -> Var("numberOfOccur", t._2)).toMap
    val rVar = states.zipWithIndex.map(t => t._1 -> Var("recognizeByq", t._2)).toMap
    val sVar = states.zipWithIndex.map(t => t._1 -> Var("startWithq", t._2)).toMap

    def output(): List[Presburger] = {
      def formulaI(): Presburger = {
        //Iに対応するqに関してのFormula
        def qFormulaI(q: Q): Presburger = {
          val fromq = dtup.filter(d => d._1._1 == q).map(d => yVar(d)).toList
          val toq = dtup.filter(t => t._2._1 == q).map(d => yVar(d)).toList
          val sub0 = Sub(AddList(toq), AddList(fromq))
          val sub1 = Sub(sVar(q), rVar(q))
          val f = Add(sub0, sub1)
          Eq(f, zero)
        }

        val qform = if(isNull) Top else AndList(states.map(q => qFormulaI(q)).toList)

        Exists(yVar.values.toSet ++ rVar.values.toSet ++ sVar.values.toSet, qform)
      }

      val first = formulaI()

      def formulaII(): Presburger = {
        def qFormulaII(q: Q): Presburger = {
          val dtoq = dtup.filter(t => t._2._1 == q)
          //q is not used in the transition
          val phiA = And(Eq(nVar(q), zero), Eq(zVar(q), mzero))
          //q is initial state
          val phi1 = And(Eq(zVar(q), zero), Eq(sVar(q), one))
          val phi2 = dtoq.map(
            t => {
              val e = Eq(zVar(q), Add(zVar(t._1._1), one))
              val yf = Lt(zero, yVar(t))
              val zf = Leq(zero, zVar(t._1._1))
              //q is not initial
              And(And(e, yf), zf)
            }
          ).toList
          val phiB = And(Lt(zero, nVar(q)), Or(phi1, OrList(phi2)))

          Or(phiA, phiB)
        }

        def nFormulaII(q: Q): Presburger = {
          val fromq = dtup.filter(t => t._1._1 == q).map(d => yVar(d)).toList
          Eq(nVar(q), Add(AddList(fromq), rVar(q)))
        }

        val qform = if(isNull) Top else AndList(states.map(q => qFormulaII(q)).toList)
        val nform = if(isNull) Top else AndList(states.map(q => nFormulaII(q)).toList)

        Exists(yVar.values.toSet ++ zVar.values.toSet ++ nVar.values.toSet, And(qform, nform))
      }

      val second = formulaII()

      def formulaIII(): Presburger = {
        //IIIに対応するFormula
        def bFormulaIII(b: Int): Presburger = {
          val i = arrId(b)
          val sum = dtup.map(d => {
            val v_b = d._2._2._1.arr(i)
            Mult(Const(v_b), yVar(d)) //List.fill(v_b)(yVar(d))
          }).toList
          Eq(xVar(b), AddList(sum))
        }

        val bform = if(isNull) Top else AndList(alphabet.map(b => bFormulaIII(b)).toList)

        //diffは全て0にならなければならないので順番,idは気にしなくていい.
        def somePosFormula(i: Int): Presburger = {
          val diff = Var("diff", i)
          val sum1 = dtup.map(d => {
            val v = d._2._2._2.arr(i)
            Mult(Const(v), yVar(d))
            /**if(v < 0) List.fill(-v)(yVar(d).copy(sign = false))
            else List.fill(v)(yVar(d))*/
          }).toList
          val form = And(Eq(diff, zero), Eq(diff, AddList(sum1)))
          Exists(yVar.values.toSet, form)
        }

        def sleFormula(sle: StrLenEquation): Presburger = {
          Eq(xVar(nameToIdx(sle.left)), xVar(nameToIdx(sle.right)))
        }

        def integerFormula(): Presburger = {
          def intFormula(i: IntegerEquation): Presburger = {
            def intTranslator(r: ReturnInteger): Integers = {
              r match{
                case c: IntC => Const(c.value)
                case v: IntV => Var("integerVariable" + v.name, -1)
                case l: StrLen => xVar.withDefaultValue(Var("not_appear", 0))(nameToIdx(l.strV))
                case oper: Operation => oper.op match{
                  case "+" => Add(intTranslator(oper.v1), intTranslator(oper.v2))
                  case "-" => Sub(intTranslator(oper.v1), intTranslator(oper.v2))
                  case "*" => {
                    (oper.v1, oper.v2) match{
                      case (c: IntC, v: IntV) => Mult(Const(c.value), Var("integerVariable" + v.name, -1))
                      case (v: IntV, c: IntC) => Mult(Const(c.value), Var("integerVariable" + v.name, -1))
                      case (c: IntC, l: StrLen) => Mult(Const(c.value), xVar.withDefaultValue(Var("not_appear", 0))(nameToIdx(l.strV)))
                      case (l: StrLen, c: IntC) => Mult(Const(c.value), xVar.withDefaultValue(Var("not_appear", 0))(nameToIdx(l.strV)))
                      case _ => {
                        println("given constraint contains non-linear fragment")
                        Const(0)
                      }
                    }
                  }
                }
              }
            }

            i.op match {
              case 1 => Eq(intTranslator(i.left), intTranslator(i.right))
              case -1 => Not(Eq(intTranslator(i.left), intTranslator(i.right)))
              case 2 => Lt(intTranslator(i.left), intTranslator(i.right))
              case -2 => Leq(intTranslator(i.right), intTranslator(i.left))
              case 3 => Lt(intTranslator(i.right), intTranslator(i.left))
              case -3 => Leq(intTranslator(i.left), intTranslator(i.right))
            }
          }
          if(ie.isEmpty) Top
          else AndList(ie.map(i => intFormula(i)).toList)
        }

        val intf = integerFormula()
        val slef = if(isNull) Top else AndList(sle.map(t => sleFormula(t)).toList)
        val spdf = if(isNull) Top else AndList((0 until wde.size).map(i => somePosFormula(i)).toList)

        Exists(yVar.values.toSet, And(And(And(bform, spdf), intf), slef))
      }

      val third = formulaIII()

      def formulaIV(): Presburger = {
        def qFormulaIV(q: Q): Presburger = {
          val sf = {
            if(q0(q)) Or(Eq(sVar(q), one), Eq(sVar(q), zero))
            else Eq(sVar(q), zero)
          }

          val rf = {
            if(finalStates(q)) Or(Eq(rVar(q), one), Eq(rVar(q), zero))
            else Eq(rVar(q), zero)
          }
          And(sf, rf)
        }

        val rsum = finalStates.map(q => rVar(q)).toList
        val rform = Eq(AddList(rsum), one)
        val ssum = q0.map(q => sVar(q)).toList
        val sform = Eq(AddList(ssum), one)

        val rs_zoro = if(isNull) Top else AndList(states.map(q => qFormulaIV(q)).toList)
        val rs_restrict = if(isNull) Top else And(rform, sform)

        Exists(rVar.values.toSet ++ sVar.values.toSet, And(rs_zoro, rs_restrict))
      }

      val forth = formulaIV()

      def formulaV(): Presburger = {
        def dFormulaV(d: ((Q, Option[A]), (Q, (IntVector, IntVector)))): Presburger = {
          Leq(zero, yVar(d))
        }

        def qFormulaV(q: Q): Presburger = {
          val zris = Leq(mzero, zVar(q))
          val nris = Leq(zero, nVar(q))
          And(zris, nris)
        }

        val y_ris = if(isNull) Top else AndList(dtup.map(d => dFormulaV(d)).toList)
        val zn_ris = if(isNull) Top else AndList(states.map(q => qFormulaV(q)).toList)

        And(y_ris, zn_ris)
      }

      val fifth = formulaV()

      List(first.reduct, second.reduct, third.reduct, forth.reduct, fifth.reduct)
    }

    def yToDelta(): Map[Var, ((Q, Option[A]), (Q, (IntVector, IntVector)))] = yVar.map(t => t._2 -> t._1)

    def zToQ(): Map[Var, Q] = zVar.map(t => t._2 -> t._1)

    def rToQ(): Map[Var, Q] = rVar.map(t => t._2 -> t._1)

    def sToQ(): Map[Var, Q] = sVar.map(t => t._2 -> t._1)
  }
}
