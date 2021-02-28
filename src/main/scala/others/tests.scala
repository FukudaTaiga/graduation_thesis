package others.tests

import java.io.File

import scala.io.Source

import formula.atomic.{IntegerEquation, StrLenEquation}
import formula.str.StrV
import formula.presburger._
import builder._
import constraint.atomicSL._
import constraint.vars._
import constraint.regular.RegCons
import constraint.wordDisEq._
import automata.transducer._
import automata.sst._
import others.matrix._


object Tests{

  //smt2はいれない.
  def getFile(name: String): String = {
    val dir = System.getProperty("user.dir") + "/benchmarks"
    val path = dir + "/" + name + ".smt2"
    val file = new File(path)
    val lines = Source.fromFile(file.getPath).getLines().toList
    val source = lines.filterNot(_.isEmpty).filterNot(_.startsWith(";")).filterNot(_.toList.forall(y => y.isWhitespace)).mkString
    source
  }

  def checker(fileName: String): Checker = {
    val source = getFile(fileName)
    Checker(source, Map())
  }
}
