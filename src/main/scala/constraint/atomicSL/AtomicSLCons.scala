package constraint.atomicSL

import constraint.vars.{SST_State, SST_Var}
import automata.sst._
import constraint.vars.TransState
import automata.transducer._

trait AtomicSLCons {
  def getLeftIdx(): Int
  def getRightIdx(): Set[Int]
}

//left  = i_1 a i_2 ... b
case class Concatenation[A](left: Int, list: List[Either[Int, A]]) extends AtomicSLCons {
  override def getLeftIdx(): Int = left
  override def getRightIdx(): Set[Int] = list.collect{case Left(i) => i}.toSet
}

//left = source.sst(replaceなど)
case class SSTConstraint[A](left: Int, sst: SST[SST_State, A, A, SST_Var], source: Int) extends AtomicSLCons {
  override def getLeftIdx(): Int = left
  override def getRightIdx(): Set[Int] = Set(source)
}

//left = fst(source)
case class TransducerConstraint[A](left: Int, fst: Transducer[TransState, A, List[A]], source: Int) extends AtomicSLCons {
  override def getLeftIdx(): Int = left
  override def getRightIdx(): Set[Int] = Set(source)
}
