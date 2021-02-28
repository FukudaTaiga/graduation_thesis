package automata.sst

import expression.regex._
import automata.automata._
import others.matrix._
import constraint.vars.{TransState, SST_State, SST_Var}
import automata.transducer._
import others.execute._

//deterministic
case class SST[Q,A,B,X](
  states: Set[Q],
  variables: Set[X],
  delta: Map[(Q,A), Option[Q]],
  eta: Map[(Q,A), Map[X, List[Either[X,B]]]],
  q0: Q,
  finalMap: Map[Q, List[Either[X,B]]],
  o: Set[B] = Set[B]()
){
  def input = delta.map(t => t._1._2).toSet
  val output = {
    if(o.isEmpty) {
      val tralp = eta.values.flatMap(t => t.values.flatMap(s => s.collect{case Right(b) => b})).toSet
      val fmalp = finalMap.values.flatMap(t => t.collect{case Right(b) => b}).toSet
      tralp ++ fmalp
    }
    else o
  }

  def domain = {
    val finalStates = finalMap.map(t => t._1).toSet
    val transition = delta.map(t => t._2 match{
      case None => ((t._1._1, Option(t._1._2)), Set[Q]())
      case Some(p) => ((t._1._1, Option(t._1._2)), Set(p))
    })
    NFA(states, transition, q0, finalStates).toDFA.toGFA.toReg.rm
  }

  def details(): Unit = {
    println("inputs is sequence of " + input)
    println("outputs is sequence of " + output)
    println("variables are " + variables)
    println("domain is " + domain)
    println("initial state is " + q0)
    for(q <- states){
      println("state : " + q)
      println("this state has transitions:")
      for(k <- delta.filter(t => t._1._1 == q).keySet){
        println("input: " + k._2)
        println("output: " + eta(k))
        for(s <- delta(k)) yield println(s)
      }
      println()
    }
    println()

    println("finalMap is ")
    for((qf, set) <- finalMap){
      println("state: " + qf + " " + "out: " + set)
    }
  }

  def assign(ls: List[Either[X,B]], env: Map[X, List[Either[X,B]]]): List[Either[X,B]] = {
    ls match{
      case Nil => Nil
      case r::rs => r match{
        case Right(b) => Right(b)::assign(rs, env)
        case Left(x) => env.withDefault(x => List(Left(x)))(x) ++ assign(rs, env)
      }
    }
  }

  //e1*e2(q,a) e1: env, e2: ins
  def composition(e1: Map[X, List[Either[X,B]]], e2: Map[X, List[Either[X,B]]]): Map[X, List[Either[X,B]]] = {
    variables.map(x => x -> assign(e2.withDefault(x => List(Left(x)))(x), e1)).toMap
  }

  def trans(q: Q, as: List[A]): Option[Q] = {
    as match{
      case Nil => Option(q)
      case a::rs => delta.withDefaultValue(None: Option[Q])(q,a) match{
        case None => None
        case Some(p) => trans(p,rs)
      }
    }
  }

  def update(q: Q, as: List[A]): Map[X, List[Either[X,B]]] = {
    as match{
      case Nil => Map[X, List[Either[X,B]]]().withDefault(x => List(Left(x)))
      case a::rs => delta(q,a) match{
        case None => Map[X, List[Either[X,B]]]().withDefault(x => List(Left(x)))
        case Some(p) => composition(eta.withDefaultValue(Map[X, List[Either[X,B]]]())(q,a), update(p,rs))
      }
    }
  }

  def accept(as: List[A]): (Boolean, List[B]) = {
    def varEli(ls: List[Either[X,B]]): List[B] = {
      ls match{
        case Nil => Nil
        case r::rs => r match{
          case Right(b) => b::varEli(rs)
          case Left(x) => varEli(rs)
        }
      }
    }

    trans(q0,as) match{
      case None => (false, Nil)
      case Some(p) => {
        finalMap.get(p) match{
          case None => (false, Nil)
          case Some(ls) => (true, varEli(assign(ls,update(q0,as))))
        }
      }
    }
  }

  def accept(str: String): (Boolean, String) = {
    val (b, ls) = accept(str.toList.map(c => c.asInstanceOf[A]))
    (b, ls.mkString)
  }

  def trim(): SST[Q,A,B,X] = trimStates.trimVars

  def toDFA(): DFA[Q,A] = DFA(states, delta.collect{case ((p, a), Some(r)) => (p,a) -> r}, q0, finalMap.keySet)

  def trimStates: SST[Q,A,B,X] = {
    val res0 = toDFA.trim
    SST(
      res0.states,
      variables,
      res0.transition.collect{case ((p, a), r) => (p,a) -> Option(r)},
      eta.filter(r => res0.transition.contains(r._1)),
      res0.q0,
      finalMap.filter(r => res0.states(r._1)),
      output
    )
  }

  def trimVars: SST[Q,A,B,X] = {
    //xから生成されうる変数のrelation nextと変数の集合v1を持って, v1から到達できる変数を返す.
    @scala.annotation.tailrec
    def star[X](next: X => Set[X])(v1: Set[X]): Set[X] = {
      val v2 = v1.flatMap(next) ++ v1
      if (v1 == v2) v1
      else star(next)(v2)
    }

    def nonRedundantVars: Set[X] = {
      def app(xs: Map[X, Set[X]], ys: Map[X, Set[X]]): Map[X, Set[X]] = variables.map(v => (v, xs.getOrElse(v, Set()) ++ ys.getOrElse(v, Set()))).toMap

      val labelx: List[Map[X, Set[X]]] = eta.toList.map(_._2.map{case (x, y) => (x, y.collect{case Left(x) => x }.toSet)})
      val label: Map[X, Set[X]] = labelx.foldLeft(Map[X, Set[X]]()){(acc, i) => app(acc, i)}
      val revlabel: Map[X, Set[X]] = variables.map{x => (x, variables.filter{y => label.withDefaultValue(Set())(y)(x)}) }.toMap
      val use: Set[X] = finalMap.flatMap(_._2).collect{case Left(x) => x}.toSet
      val nonempty: Set[X] = eta.toList.flatMap(_._2).filter{r => r._2.exists(_.isRight)}.map(_._1).toSet

      star(label)(use).intersect(star(revlabel)(nonempty))
    }

    val newVars: Set[X] = if(delta.isEmpty) Set() else nonRedundantVars

    //val newVars = usedVars.intersect(nonEmptyVars)
    val newEta = eta.map(
      r => r._1 -> r._2.filter(x => newVars(x._1)).map(x => x._1 -> x._2.filter(e => (e.isRight) || (e.isLeft && newVars(e.left.get))))
    ).withDefaultValue(newVars.map(x => x -> List()).toMap.withDefaultValue(List()))

    val newF = finalMap.map(t => t._1 -> t._2.filter(e => (e.isRight) || (e.isLeft && newVars(e.left.get))))

    SST(states, newVars, delta, newEta, q0, newF, output)
  }

  def renameInt(): SST[Int, A, B, X] = {
    val toNewState: Map[Q, Int] = states.zipWithIndex.map(x => x._1 -> x._2).toMap

    val newStates: Set[Int] = states.map(s => toNewState(s))

    val newQ0: Int = toNewState.withDefaultValue(-1)(q0)

    val newDelta: Map[(Int, A), Option[Int]] = delta.collect{case ((p,a), Some(r)) => (toNewState(p), a) -> Option(toNewState(r))} //map(r => (toNewState(r._1._1), r._1._2) -> toNewState(r._2))

    val newEta: Map[(Int, A), Map[X, List[Either[X, B]]]] = eta.map(r => (toNewState(r._1._1), r._1._2) -> r._2)

    val newF: Map[Int, List[Either[X, B]]] = finalMap.map(r => toNewState(r._1) -> r._2)

    SST(newStates, variables, newDelta, newEta, newQ0, newF, output)
  }

  def rename(sstName: String): SST[SST_State, A, B, SST_Var] = {

    val toNewState: Map[Q, SST_State] = (states + q0).toList.zipWithIndex.map(x => x._1 -> SST_State(x._2, sstName)).toMap

    val toNewVar: Map[X, SST_Var] = variables.toList.zipWithIndex.map(x => x._1 -> SST_Var(x._2, sstName)).toMap

    val newStates: Set[SST_State] = states.map(s => toNewState(s))

    val newQ0: SST_State = toNewState.withDefaultValue(SST_State(0, sstName))(q0)

    val newVars: Set[SST_Var] = variables.map(x => toNewVar(x))

    val newDelta: Map[(SST_State, A), Option[SST_State]] = delta.collect{case ((p,a), Some(r)) => (toNewState(p), a) -> Option(toNewState(r))} //map(r => (toNewState(r._1._1), r._1._2) -> toNewState(r._2))

    val newEta: Map[(SST_State, A), Map[SST_Var, List[Either[SST_Var, B]]]] = eta.map(r =>
      (toNewState(r._1._1), r._1._2) -> r._2.map(
        t => toNewVar(t._1) -> t._2.map(
          e => if (e.isLeft) Left(toNewVar(e.left.get)) else Right(e.right.get)
        )
      )
    )

    val newF: Map[SST_State, List[Either[SST_Var, B]]] = finalMap.map(r =>
      toNewState(r._1) -> r._2.map(
        e => if (e.isLeft) Left(toNewVar(e.left.get)) else Right(e.right.get)
      )
    )

    SST(newStates, newVars, newDelta, newEta, newQ0, newF, output)
  }

  def varSet(ls: List[Either[X,B]]): Set[X] = {
    ls.collect{case Left(x) => x}.toSet
  }

  def alphaSet(ls: List[Either[X,B]]): Set[B] = {
    ls.collect{case Right(b) => b}.toSet
  }

  def parikhx(ls: List[Either[X,B]], v: X): Int = {
    @scala.annotation.tailrec
    def parikh(ls: List[Either[X,B]], v: X, n: Int): Int = {
      ls match{
        case Nil => n
        case a::rs => {
          a match{
            case Right(c) => parikh(rs, v, n)
            case Left(z) => if(z == v) parikh(rs, v, n + 1) else parikh(rs, v, n)
          }
        }
      }
    }
    parikh(ls, v, 0)
  }

  def parikhb(ls: List[Either[X,B]], v: B): Int = {
    @scala.annotation.tailrec
    def parikh(ls: List[Either[X,B]], v: B, n: Int): Int = {
      ls match{
        case Nil => n
        case a::rs => {
          a match{
            case Right(c) => if(c == v) parikh(rs, v, n + 1) else parikh(rs, v, n)
            case Left(z) => parikh(rs, v, n)
          }
        }
      }
    }
    parikh(ls, v, 0)
  }

  //もらったsetにindexをつけて、対応する番号のArrayにparikh imageを収納していく
  def xistToVector(ls: List[Either[X,B]], set: Set[X]): IntVector = {
    val idx = set.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size)(i => parikhx(ls, idx(i)))
    new IntVector(set.size, arr.toVector)
  }

  def bistToVector(ls: List[Either[X,B]], set: Set[B]): IntVector = {
    val idx = set.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size)(i => parikhb(ls, idx(i)))
    new IntVector(set.size, arr.toVector)
  }

  def parikhMx(m: Map[X, List[Either[X,B]]], x: X, y: X): Int = {
    parikhx(m.withDefault(z => List(Left(z)))(x), y)
  }

  def parikhMb(m: Map[X, List[Either[X,B]]], x: X, b: B): Int = {
    parikhb(m.withDefault(z => List(Left(z)))(x), b)
  }

  //rowがもらったsetのindex,lineがvariablesのindexに(Mxgでvariableを写した時の返される文字列のparikh imageをいれる)なる.
  def xapToMatrix(m: Map[X, List[Either[X,B]]], set: Set[X]): IntMatrix = {
    val row = set.zipWithIndex.map(t => t._2->t._1).toMap
    val column = variables.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size, variables.size)((i,j) => parikhMx(m, column(j), row(i)))
    new IntMatrix(set.size, variables.size, arr.map(row => row.toVector).toVector)
  }
  def bapToMatrix(m: Map[X, List[Either[X,B]]], set: Set[B]): IntMatrix = {
    val row = set.zipWithIndex.map(t => t._2->t._1).toMap
    val column = variables.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size, variables.size)((i,j) => parikhMb(m, column(j), row(i)))
    new IntMatrix(set.size, variables.size, arr.map(row => row.toVector).toVector)
  }

  def toParikh(): MxgTransducer[Option[(Q, IntVector)],A,B] = {
    type State = Option[(Q, IntVector)]
    type Maptype = Map[(State, Option[A]), Set[(State, Option[IntVector])]]
    val tfs = Set[State](None)
    @scala.annotation.tailrec
    def makeStates(list: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      list match{
        case Nil => (res0, res1)
        case q::rs => {
          val newMap = delta.collect{ case ((p,a), Some(r)) if r == q.get._1 =>
            val m = eta.withDefaultValue(Map[X, List[Either[X,B]]]())(p,a)
            val mV = xapToMatrix(m, variables)
            val mB = bapToMatrix(m, output)
            val from = (Option((p, q.get._2.proM(mV))), Option(a))
            val vector = Option(q.get._2.proM(mB))
            from -> (res1.getOrElse(from, Set()) + ((q, vector)))
          }.toMap
          val newStates = newMap.keySet.map(s => s._1)
          val s = (newStates diff res0).toList
          makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val toNone = finalMap.map(t =>
      {
        val ftate = Option((t._1, xistToVector(t._2, variables)))
        val vector = Option(bistToVector(t._2, output))
        (ftate, None: Option[A]) -> Set((None: State, vector))
      }
    )

    val (tstates, tdelta) = makeStates(toNone.keySet.map(k => k._1).toList, toNone.keySet.map(k => k._1) + None, toNone)

    val tq0 = tstates.collect{ case Some((q,v)) if q == q0 => Option(q,v) }

    new MxgTransducer(tstates, tdelta, tq0, tfs, output)
  }

  //iは0から. i番目の変数 x0#...#xi#...#xn# のxiを取ってくる.
  def changeFinalMap(i: Int, split: B): SST[Q,A,B,X] = {
    @scala.annotation.tailrec
    def getIth(ls: List[Either[X,B]], k: Int, res: List[Either[X,B]]): List[Either[X,B]] = {
      if(i < k) Nil
      else{
        ls match{
          case Nil => res
          case e::rs => {
            if(k == i){
              if(e == Right(split)) res else getIth(rs, k, res :+ e)
            }
            else{
              if(e == Right(split)) getIth(rs, k + 1, res) else getIth(rs, k, res)
            }
          }
        }
      }
    }

    val newFinalMap = finalMap.map(t => t._1 -> getIth(t._2, 0, Nil))
    SST(states, variables, delta, eta, q0, newFinalMap, output)
  }

  //vで終わる部分文字列を返す
  def listEndx(ls: List[Either[X,B]], v: X): Set[List[Either[Option[X],B]]] = {
    @scala.annotation.tailrec
    def lsEndv(ls: List[Either[X,B]], v: X, res: Set[List[Either[Option[X], B]]], corr: List[Either[Option[X], B]]): Set[List[Either[Option[X],B]]] = {
      ls match{
        case Nil => res
        case a::rs => {
          a match{
            case Right(c) => lsEndv(rs, v, res, corr :+ Right(c))
            case Left(y) => if(y == v) lsEndv(rs, v, res + (corr :+ Left(None)), corr :+ Left(Option(y))) else lsEndv(rs, v, res, corr :+ Left(Option(y)))
          }
        }
      }
    }
    lsEndv(ls, v, Set(), Nil)
  }
  def listEndb(ls: List[Either[X,B]], v: B): Set[List[Either[Option[X],B]]] = {
    @scala.annotation.tailrec
    def lsEndv(ls: List[Either[X,B]], v: B, res: Set[List[Either[Option[X], B]]], corr: List[Either[Option[X], B]]): Set[List[Either[Option[X],B]]] = {
      ls match{
        case Nil => res
        case a::rs => {
          a match{
            case Right(c) => if(c == v) lsEndv(rs, v, res + (corr :+ Right(c)), corr :+ Right(c)) else lsEndv(rs, v, res, corr :+ Right(c))
            case Left(y) => lsEndv(rs, v, res, corr :+ Left(Option(y)))
          }
        }
      }
    }
    lsEndv(ls, v, Set(), Nil)
  }

  def adjust(m: Map[X, List[Either[X,B]]]): Map[Option[X], List[Either[Option[X],B]]] = {
    def adjustl(ls: List[Either[X,B]]): List[Either[Option[X],B]] = {
      ls match{
        case Nil => Nil
        case v::rs => v match{
          case Left(x) => Left(Option(x))::adjustl(rs)
          case Right(b) => Right(b)::adjustl(rs)
        }
      }
    }

    m.map(t => (Option(t._1)->adjustl(t._2)))
  }

  //Noneに終わりの文字に入っている可能性のある文字列を入れておく.
  def toCountSST(b: B): NSST[(Q,Option[X]),A,B,Option[X]] = {
    type State = (Q,Option[X])
    type Maptype = Map[(State,Option[A]), Set[(State, Map[Option[X], List[Either[Option[X],B]]])]]
    val none = None: Option[X]

    val cq0 = (q0, none)
    val cfm1 = finalMap.map(t => (t._1, none) -> listEndb(t._2, b))
    val cfm2 = finalMap.flatMap(t => variables.map(x => (t._1, Option(x)) -> listEndx(t._2, x))).toMap
    val cfm = cfm1.filterNot(t => t._2.isEmpty) ++ cfm2.filterNot(t => t._2.isEmpty)
    val cvariables = variables.map(x => Option(x)) + none
    @scala.annotation.tailrec
    def makeStates(list: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      list match{
        case Nil => (res0, res1)
        case q::rs => {
          q._2 match{
            //(p, none)->Set((q,None))
            case None => {
              val keys = delta.filter(t => t._2 == Some(q._1)).keySet
              val newMap = keys.map(
                k => {
                  val tup = ((k._1, none), Option(k._2))
                  tup -> (res1.getOrElse(tup, Set()) + ((q, adjust(eta(k)))))
                }
              ).toMap
              val newStates = newMap.keySet.map(t => t._1)
              val s = (newStates diff res0).toList
              makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
            }
            case Some(x) => {
              val keys = delta.filter(t => t._2 == Some(q._1)).keySet
              //(p,y)-a/m->(q,x), m(x) = wyw
              val varToVar = keys.map(
                k => {
                  val ys = variables.filter(u => varSet(eta(k).withDefault(x => List(Left(x)))(u))(x))
                  ys.map(
                    y => {
                      val tup = ((k._1, Option(y)), Option(k._2))
                      val set = listEndx(eta(k).withDefault(x => List(Left(x)))(y), x).map(ls => (q, adjust(eta(k)) + (none -> ls)))
                      tup -> (res1.getOrElse(tup, Set()) ++ set)
                    }
                  )
                }
              ).flatten.toMap
              //(p,none)-a/m->(q,x)
              val noneToVar = keys.map(
                k => {
                  val tup = ((k._1, none), Option(k._2))
                  val lset = listEndb(eta(k).withDefault(x => List(Left(x)))(x), b).map(ls => (q, adjust(eta(k)) + (none -> ls)))
                  tup -> (res1.getOrElse(tup, Set()) ++ lset)
                }
              ).toMap
              val newMap = varToVar ++ noneToVar
              val newStates = newMap.keySet.map(t => t._1)
              val s = (newStates diff res0).toList
              makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
            }
          }
        }
      }
    }

    val (cstates, cdelta) = makeStates(cq0 :: cfm.keySet.toList, cfm.keySet + cq0, Map())

    NSST(cstates, cvariables, cdelta, cq0, cfm)
  }

  def toCountSST(bs: Set[B]): NSST[(Q,Option[X]),A,B,Option[X]] = {
    type State = (Q,Option[X])
    type Maptype = Map[(State,Option[A]), Set[(State, Map[Option[X], List[Either[Option[X],B]]])]]
    val none = None: Option[X]

    def listEndbs(ls: List[Either[X,B]], set: Set[B]): Set[List[Either[Option[X],B]]] = {
      set.flatMap(b => listEndb(ls, b))
    }

    val cq0 = (q0, none)
    val cfm1 = finalMap.map(t => (t._1, none) -> listEndbs(t._2, bs))
    val cfm2 = finalMap.flatMap(t => variables.map(x => (t._1, Option(x)) -> listEndx(t._2, x))).toMap
    val cfm = cfm1.filterNot(t => t._2.isEmpty) ++ cfm2.filterNot(t => t._2.isEmpty)
    val cvariables = variables.map(x => Option(x)) + none
    @scala.annotation.tailrec
    def makeStates(list: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      list match{
        case Nil => (res0, res1)
        case q::rs => {
          val keys = delta.filter(t => t._2 == Some(q._1)).keySet
          q._2 match{
            //(p, none)->Set((q,None))
            case None => {
              val newMap = keys.map(
                k => {
                  val tup = ((k._1, none), Option(k._2))
                  tup -> (res1.getOrElse(tup, Set()) + ((q, adjust(eta(k)))))
                }
              ).toMap
              val newStates = newMap.keySet.map(t => t._1)
              val s = (newStates diff res0).toList
              makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
            }
            case Some(x) => {
              //(p,y)-a/m->(q,x), m(x) = wyw
              val varToVar = keys.map(
                k => {
                  val ys = variables.filter(u => varSet(eta(k)(u))(x))
                  ys.map(
                    y => {
                      val tup = ((k._1, Option(y)), Option(k._2))
                      val set = listEndx(eta(k)(y), x).map(ls => (q, adjust(eta(k)) + (none -> ls)))
                      tup -> (res1.getOrElse(tup, Set()) ++ set)
                    }
                  )
                }
              ).flatten.toMap
              //(p,none)-a/m->(q,x)
              val noneToVar = keys.map(
                k => {
                  val tup = ((k._1, none), Option(k._2))
                  val lset = listEndbs(eta(k)(x), bs).map(ls => (q, adjust(eta(k)) + (none -> ls)))
                  tup -> (res1.getOrElse(tup, Set()) ++ lset)
                }
              ).toMap
              val newMap = varToVar ++ noneToVar
              val newStates = newMap.keySet.map(t => t._1)
              val s = (newStates diff res0).toList
              makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
            }
          }
        }
      }
    }

    val (cstates, cdelta) = makeStates(cq0 :: cfm.keySet.toList, cfm.keySet + cq0, Map())

    NSST(cstates, cvariables, cdelta, cq0, cfm)
  }
}

//nondeterministic
case class NSST[Q,A,B,X](
  states: Set[Q],
  variables: Set[X],
  delta: Map[(Q,Option[A]), Set[(Q, Map[X, List[Either[X,B]]])]],
  q0: Q,
  fm: Map[Q, Set[List[Either[X,B]]]]
){
  def input = delta.keySet.collect{case (q, Some(a)) => a}
  val output = delta.values.flatten.flatMap(t => t._2.values.flatMap(s => s.collect{case Right(b) => b})).toSet

  val finalMap = fm.withDefaultValue(Set())

  def domain = {
    val finalStates = finalMap.keySet
    val transition = delta.collect{case ((q,a),set) => ((q,a)->set.map(t => t._1))}
    NFA[Q,A](states, transition, q0, finalStates).toDFA.toGFA.toReg.rm
  }

  def details(): Unit = {
    println("inputs is sequence of " + input)
    println("outputs is sequence of " + output)
    println("variables are " + variables)
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

    println("finalMap is ")
    for((qf, set) <- finalMap){
      println("state: " + qf + " " + "out: " + set)
    }
  }

  def assign(ls: List[Either[X,B]], env: Map[X, List[Either[X,B]]]): List[Either[X,B]] = {
    ls match{
      case Nil => Nil
      case r::rs => r match{
        case Right(b) => Right(b)::assign(rs, env)
        case Left(x) => env.withDefault(x => List(Left(x)))(x) ++ assign(rs, env)
      }
    }
  }

  //e1*e2(q,a) e1: env, e2: ins
  def composition(e1: Map[X, List[Either[X,B]]], e2: Map[X, List[Either[X,B]]]): Map[X, List[Either[X,B]]] = {
    //e2.map(t => t._1 -> assign(t._2, e1))
    variables.map(x => x -> assign(e2.withDefault(x => List(Left(x)))(x), e1)).toMap
  }

  def transition(qs: Set[Q], as: List[A]): Set[(Q, Map[X, List[Either[X,B]]])] = {
    def subtransition(set: Set[(Q, Map[X, List[Either[X,B]]])], as: List[A]): Set[(Q, Map[X, List[Either[X,B]]])] = {
      as match{
        case Nil => set
        case a::rs => {
          val ns = set.flatMap(t => delta.withDefaultValue(Set[(Q, Map[X, List[Either[X,B]]])]())(t._1, Option(a)).map(s => (s._1, composition(t._2, s._2))))
          subtransition(ns, rs)
        }
      }
    }
    subtransition(qs.map(q => (q, Map[X, List[Either[X,B]]]().withDefault(x => List(Left(x))))), as)
  }

  def accept(as: List[A]): (Boolean, Set[List[B]]) = {
    def varEli(ls: List[Either[X,B]]): List[B] = {
      ls match{
        case Nil => Nil
        case r::rs => r match{
          case Right(b) => b::varEli(rs)
          case Left(x) => varEli(rs)
        }
      }
    }

    val outstring = transition(Set(q0), as).filter(t => finalMap.keySet(t._1)).flatMap(s => finalMap(s._1).map(ls => varEli(assign(ls, s._2))))
    if(outstring.isEmpty)(false, Set(Nil))else(true, outstring)
  }

  def accept(str: String): (Boolean, String) = {
    val (b, ls) = accept(str.toList.map(c => c.asInstanceOf[A]))
    (b, ls.mkString)
  }

  def rename(sstName: String): NSST[SST_State, A, B, SST_Var] = {
    val toNewState: Map[Q, SST_State] = (states + q0).toList.zipWithIndex.map(x => x._1 -> SST_State(x._2, sstName)).toMap

    val toNewVar: Map[X, SST_Var] = variables.toList.zipWithIndex.map(x => x._1 -> SST_Var(x._2, sstName)).toMap

    val newStates: Set[SST_State] = states.map(s => toNewState(s))

    val newQ0: SST_State = toNewState.withDefaultValue(SST_State(0, sstName))(q0)

    val newVars: Set[SST_Var] = variables.map(x => toNewVar(x))

    def toNewMap(m: Map[X, List[Either[X, B]]]): Map[SST_Var, List[Either[SST_Var, B]]] = {
      m.map(
        r => {
          val newList = r._2.map(e => if(e.isLeft) Left(toNewVar(e.left.get)) else Right(e.right.get))
          toNewVar(r._1) -> newList
        }
      )
    }

    val newDelta: Map[(SST_State, Option[A]), Set[(SST_State, Map[SST_Var, List[Either[SST_Var, B]]])]] = {
      delta.collect{
        case ((q, op1), set) => {
          val newSet = set.map(t => (toNewState(t._1), toNewMap(t._2)))
          (toNewState(q), op1) -> newSet
        }
      }
    }

    val newF: Map[SST_State, Set[List[Either[SST_Var, B]]]] = finalMap.map(r =>
      toNewState(r._1) -> r._2.map(
        ls => ls.map(e => if(e.isLeft) Left(toNewVar(e.left.get)) else Right(e.right.get))
      )
    )

    NSST(newStates, newVars, newDelta, newQ0, newF)
  }

  def varSet(ls: List[Either[X,B]]): Set[X] = {
    ls.collect{case Left(x) => x}.toSet
  }

  def alphaSet(ls: List[Either[X,B]]): Set[B] = {
    ls.collect{case Right(b) => b}.toSet
  }

  def parikhx(ls: List[Either[X,B]], v: X): Int = {
    require(variables(v))
    ls match{
      case Nil => 0
      case a::rs => {
        a match{
          case Right(c) => parikhx(rs, v)
          case Left(z) => if(z == v) 1 + parikhx(rs, v) else parikhx(rs, v)
        }
      }
    }
  }

  def parikhb(ls: List[Either[X,B]], v: B): Int = {
    require(output(v))
    ls match{
      case Nil => 0
      case a::rs => {
        a match{
          case Right(c) => if(c == v) 1 + parikhb(rs, v) else parikhb(rs, v)
          case Left(z) => parikhb(rs, v)
        }
      }
    }
  }

  //もらったsetにindexをつけて、対応する番号のArrayにparikh imageを収納していく
  def xistToVector(ls: List[Either[X,B]], set: Set[X]): IntVector = {
    //require(set match{case v: Set[X] => true; case v: Set[B] => true;case _ => false})

    val idx = set.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size)(i => parikhx(ls, idx(i)))
    new IntVector(set.size, arr.toVector)
  }

  def bistToVector(ls: List[Either[X,B]], set: Set[B]): IntVector = {
    //require(set match{case v: Set[X] => true; case v: Set[B] => true;case _ => false})

    val idx = set.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size)(i => parikhb(ls, idx(i)))
    new IntVector(set.size, arr.toVector)
  }

  def parikhMx(m: Map[X, List[Either[X,B]]], x: X, y: X): Int = {
    parikhx(m.withDefault(x => List(Left(x)))(x), y)
  }

  def parikhMb(m: Map[X, List[Either[X,B]]], x: X, b: B): Int = {
    parikhb(m.withDefault(x => List(Left(x)))(x), b)
  }

  //rowがもらったsetのindex,lineがvariablesのindexに(Mxgでvariableを写した時の返される文字列のparikh imageをいれる)なる.
  def xapToMatrix(m: Map[X, List[Either[X,B]]], set: Set[X]): IntMatrix = {
    require(set.subsetOf(variables))

    val row = set.zipWithIndex.map(t => t._2->t._1).toMap
    val column = variables.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size, variables.size)((i,j) => parikhMx(m, column(j), row(i)))
    new IntMatrix(set.size, variables.size, arr.map(row => row.toVector).toVector)
  }
  def bapToMatrix(m: Map[X, List[Either[X,B]]], set: Set[B]): IntMatrix = {
    require(set.subsetOf(output))

    val row = set.zipWithIndex.map(t => t._2->t._1).toMap
    val column = variables.zipWithIndex.map(t => t._2->t._1).toMap
    val arr = Vector.tabulate(set.size, variables.size)((i,j) => parikhMb(m, column(j), row(i)))
    new IntMatrix(set.size, variables.size, arr.map(row => row.toVector).toVector)
  }

  def toParikh(): MxgTransducer[Option[(Q, IntVector)],A,B] = {
    type State = Option[(Q, IntVector)]
    type Maptype = Map[(State, Option[A]), Set[(State, Option[IntVector])]]
    val tfs = Set[State](None)
    @scala.annotation.tailrec
    def makeStates(list: List[State], res0: Set[State], res1: Maptype): (Set[State], Maptype) = {
      list match{
        case Nil => (res0, res1)
        case q::rs => {
          val newMap = delta.collect { case ((p,a), set) =>
            val tups = set.collect {
              case (r, m) if r == q.get._1 => {
                val mV = xapToMatrix(m, variables)
                val mB = bapToMatrix(m, output)
                val vector = Option(q.get._2.proM(mB))
                val v = q.get._2.proM(mV)
                (v, (q, vector))
              }
            }.groupBy(t => t._1).map(s => s._1 -> s._2.map(u => u._2))
            tups.map{t =>
              val from = (Option((p, t._1)), a)
              from -> (res1.getOrElse(from, Set()) ++ t._2)
            }
          }.flatten.toMap
          val newStates = newMap.keySet.map(s => s._1)
          val s = (newStates diff res0).toList
          makeStates(s ++ rs, res0 ++ newStates, res1 ++ newMap)
        }
      }
    }

    val toNone = finalMap.flatMap(t =>
      {
        val ftates = t._2.map(l => Option((t._1, xistToVector(l, variables))))
        val vectors = t._2.map(l => (None: State, Option(bistToVector(l, output))))
        var map: Maptype = Map()
        for(s <- ftates) {
          val ft = (s, None: Option[A])
          map += ft -> (map.getOrElse(ft, Set()) ++ vectors)
        }
        map
      }
    )

    val (tstates, tdelta) = makeStates(toNone.keySet.map(k => k._1).toList, toNone.keySet.map(k => k._1) + None, toNone)

    val tq0 = tstates.collect{ case Some((q,v)) if q == q0 => Option((q,v)) }

    new MxgTransducer(tstates, tdelta, tq0, tfs, output)
  }
}

object SSTExample0{
  val states = Set(0,1)
  val input = Set('a','b','$')
  val output = Set('a','b','c', 'd')
  val variables = Set('x','y')
  val delta = Map((0,'a') -> Option(0),(0,'b') -> Option(0),(0,'$') -> Option(1))
  val zza = Map('x'->List(Left('x'),Right('a')),'y'->List(Right('a'),Left('y')))
  val zzb = Map('x'->List(Left('x'),Right('b')),'y'->List(Right('b'),Left('y')))
  val zo$ = Map('x'->List(Left('x')), 'y'->List(Left('y')))
  val eta = Map((0,'a')->zza, (0,'b')->zzb, (0,'$')->zo$)
  val q0 = 0
  val finalMap = Map(1 -> List[Either[Char,Char]](Left('x'),Left('y')))
  //入力とその反転を連結したものを返す
  val sst = SST(states, variables, delta, eta, q0, finalMap)
  val tparikh = sst.toParikh
  def csst(a: Char) = sst.toCountSST(a)
}

object SSTExample1{
  val states = Set(0,1)
  val input = Set('a','b','#')
  val output = Set('a','b', 'c', 'd')
  val variables = Set('x')
  val delta = Map((0,'a')-> Option(0),(0,'b')-> Option(0), (0,'#')-> Option(1), (1,'a')-> Option(1),(1,'b')-> Option(1))
  val zza = Map('x'->List(Left('x'),Right('a')))
  val zzb = Map('x'->List(Left('x'),Right('b')))
  val zohash = Map('x'->List(Left('x'),Left('x')))
  val ooa = Map('x'->List(Left('x'),Right('a')))
  val oob = Map('x'->List(Left('x'),Right('b')))
  val eta = Map((0,'a')->zza, (0,'b')->zzb, (0,'#')->zohash, (1,'a')->ooa, (1,'b')->oob)
  val q0 = 0
  val finalMap = Map(1 -> List[Either[Char,Char]](Left('x')))
  val sst = SST(states, variables, delta, eta, q0, finalMap)
  val tparikh = sst.toParikh
  def csst(a: Char) = sst.toCountSST(a)
}

object SSTExample2{
  val states1 = Set(0,1)
  val input1 = Set('a','b','$')
  val output1 = Set('a','b')
  val variables1 = Set('x','y')
  val delta1 = Map((0,'a') -> Option(0),(0,'b') -> Option(0),(0,'$') -> Option(1))
  val zza1 = Map('x'->List(Left('x'),Right('a')),'y'->List(Right('a'),Left('y')))
  val zzb1 = Map('x'->List(Left('x'),Right('b')),'y'->List(Right('b'),Left('y')))
  val zo$1 = Map('x'->List(Left('x')), 'y'->List(Left('y')))
  val eta1 = Map((0,'a')->zza1, (0,'b')->zzb1, (0,'$')->zo$1)
  val q01 = 0
  val finalMap1 = Map(1 -> List[Either[Char,Char]](Left('x'),Right('a'), Right('a'), Left('y')))
  //入力とその反転を連結したものを返す
  val sst1 = SST(states1, variables1, delta1, eta1, q01, finalMap1)
  val tparikh1 = sst1.toParikh
  val cssta1 = sst1.toCountSST('a')
  val tparikha1 = cssta1.toParikh

  val states2 = Set(0,1)
  val input2 = Set('a','b','#')
  val output2 = Set('a','b')
  val variables2 = Set('x')
  val delta2 = Map((0,'a')-> Option(0),(0,'b')-> Option(0), (0,'#')-> Option(1), (1,'a')-> Option(1),(1,'b')-> Option(1))
  val zza2 = Map('x'->List(Left('x'),Right('a')))
  val zzb2 = Map('x'->List(Left('x'),Right('b')))
  val zohash2 = Map('x'->List(Left('x'),Left('x')))
  val ooa2 = Map('x'->List(Left('x'),Right('a')))
  val oob2 = Map('x'->List(Left('x'),Right('b')))
  val eta2 = Map((0,'a')->zza2, (0,'b')->zzb2, (0,'#')->zohash2, (1,'a')->ooa2, (1,'b')->oob2)
  val q02 = 0
  val finalMap2 = Map(1 -> List[Either[Char,Char]](Left('x')))
  val sst2 = SST(states2, variables2, delta2, eta2, q02, finalMap2)
  val tparikh2 = sst2.toParikh
  val csstb2 = sst2.toCountSST('b')
  val tparikhb2 = csstb2.toParikh

  val subt = tparikh1.subtract(tparikh2)
  val subabt = tparikha1.subtract(tparikhb2)
}
