package constraint.wordDisEq

import constraint.vars.{SST_State, SST_Var}
import automata.sst._
import constraint.vars.TransState
import automata.transducer._

case class WordDisEq(left: Int, right: Int){
  def getLeftIdx: Int = left
  def getRightIdx: Int = right
}

/**
//left  != i_1 a i_2 ... b
case class DisConcatenation[A](left: Int, list: List[Either[Int, A]]) extends WordDisEq {
  override def getLeftIdx(): Int = left
}

//left != source.sst(replaceなど)
case class DisSSTConstraint[A](left: Int, sst: SST[SST_State, A, A, SST_Var], source: Int) extends WordDisEq {
  override def getLeftIdx(): Int = left
}

//left != fst(source)
case class DisTransducerConstraint[A](left: Int, fst: Transducer[TransState, A, List[A]], source: Int) extends WordDisEq {
  override def getLeftIdx(): Int = left
}*/
