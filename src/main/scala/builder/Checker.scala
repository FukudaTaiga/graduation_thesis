package builder

import java.io.{File, PrintWriter}

import constraint.atomicSL.AtomicSLCons
import constraint.regular.RegCons
import constraint.wordDisEq._
import constraint.vars._
import formula.atomic._
import formula.str.StrV
import automata.sst._
import automata.transducer._

import scala.sys.process._

case class Checker(source: String, options: Map[String, List[String]]) {
  type MySST[X] = SST[SST_State, Char, X, SST_Var]
  type Clause = (List[AtomicSLCons], Set[RegCons[Char]], Set[Char], Set[IntegerEquation], Set[StrLenEquation], Set[WordDisEq], Map[StrV, Int])

  val (formula, getModel) = FormulaBuilder(source).output
  val clauses: List[Clause] = SLConsBuilder(formula).output
  val printOption: Boolean = options.contains("-p")

  def output: (Boolean, String) = {
    //val start = System.currentTimeMillis()
    val (b, str) = loopCheck(clauses)
    //val end = System.currentTimeMillis()
    //println(end - start)
    (b, str)
  }

  def loopCheck(clauses: List[Clause]): (Boolean, String) = {
    clauses match {
      case Nil => {
        (false, "")
      }
      case x :: xs => {
        val (sat, witness) = check(x)
        if(sat){
          (sat, witness)
        }
        else {
          loopCheck(xs)
        }
      }
    }
  }

  def check(clause: Clause): (Boolean, String) = {
    val (we, sr, chars0, ie, sle, wde, nameToIdx) = clause
    val asciiSize = if(options.contains("-ascii")) options("-ascii").head.toInt else 0
    val ascii = Math.min(256, asciiSize)
    val chars = chars0 ++ List.range(0, ascii).map(_.toChar).toSet
    val split = 35.toChar
    val getLength = (ie.flatMap(t => t.strVs).intersect(nameToIdx.keySet).nonEmpty) || sle.nonEmpty
    val intOnly = (ie.flatMap(t => t.strVs).intersect(nameToIdx.keySet).isEmpty) && we.isEmpty && sr.isEmpty
    val (sstList, sstInt, sstChar, sstSet, sstSat) = {
      if(printOption){
        println("sstbuild start")
        val sstTimeS = System.currentTimeMillis()
        val (a, b, c, d, e) = SSTBuilder(we, sr, wde, chars, split, nameToIdx, getModel, getLength).output
        val sstTimeE = System.currentTimeMillis()
        println(s"sstbuild finish: ${(sstTimeE - sstTimeS) / 1000.0}s")
        (a,b,c,d,e)
      }
      else SSTBuilder(we, sr, wde, chars, split, nameToIdx, getModel, getLength, printOption).output
    }

    if(printOption){
      sstChar.eta.groupBy(t => t._1._1).foreach(
        u => {
          println(s"state: ${u._1}")
          u._2.foreach(t => {
            if(sstChar.delta(t._1).isEmpty) println(s"state: ${t._1} ->  ")
            else println(s"state: ${t._1} -> ${sstChar.delta(t._1).get}")
            t._2.foreach(u => println(s"--var: ${u._1} => ${u._2}"))
            println()
          })
        }
      )
    }

    def loopCS(wde: Set[(MySST[Char], MySST[Char])]): (Boolean, String) = {
      @scala.annotation.tailrec
      def bfs(wde: List[(MySST[Char], MySST[Char])], preTrans: TupleTransducer[TransState, Char, Int], n: Int, list: List[Set[Char]], res: Map[Int, (Set[Char], Boolean)]):
      (Boolean, String) = {
        if(n == wde.size) {
          val (presburgers, trans, yToDelta, zToQ, sToQ, rToQ) = PresburgerBuilder(sstInt, preTrans, ie, sle, chars, wde, nameToIdx, res).output
          if(printOption){
            println(s"characterSize: ${chars.size}")
            println(s"sstStateSize: ${sstInt.states.size}")
            println(s"sstVariables: ${sstInt.variables.size}")
            println(s"sstDeltaSize: ${sstInt.delta.size}")
            println(s"transStatesSize: ${trans.states.size}")
            println(s"transTransitionSize: ${yToDelta.size}")
          }
          val z3Input = Z3InputBuilder(presburgers, getModel).output
          val z3Output = {
            if(printOption){
              println("z3 start")
              val z3TimeS = System.currentTimeMillis()
              val z = executeZ3(z3Input)
              val z3TimeE = System.currentTimeMillis()
              println(s"z3 finish: ${(z3TimeE - z3TimeS) / 1000.0}s")
              z
            }
            else executeZ3(z3Input)
          }
          if(z3Output.startsWith("sat")){
            if(getModel){
              val witness = WitnessBuilder(z3Output, nameToIdx, yToDelta, zToQ, sToQ, rToQ, sstChar, trans, chars, split, intOnly).output
              (true, witness)
            }
            else (true, "")
          }
          else (false, "")
        }
        else {
          val lst = wde.take(n + 1)
          list match{
            case Nil => (false, "")
            case s::rs => {
              val resp = res + (n -> (s, true))
              val (presburgers, trans, yToDelta, zToQ, sToQ, rToQ) = PresburgerBuilder(sstInt, preTrans, ie, sle, chars, lst, nameToIdx, resp).output
              val z3Input = Z3InputBuilder(presburgers, getModel).output
              val z3Output = executeZ3(z3Input)
              if(z3Output.startsWith("sat")) bfs(wde, trans, n + 1, chars :: Nil, resp)
              else{
                val resd = res + (n -> (s, false))
                val (presburgersn, transn, yToDeltan, zToQn, sToQn, rToQn) = PresburgerBuilder(sstInt, preTrans, ie, sle, chars, lst, nameToIdx, resd).output
                val z3Inputn = Z3InputBuilder(presburgersn, getModel).output
                val z3Outputn = executeZ3(z3Inputn)
                if(z3Outputn.startsWith("sat")) bfs(wde, trans, n + 1, chars :: Nil, resd)
                else{
                  val subset = s.drop(s.size / 2)
                  val other = s diff subset
                  if(subset.size == 1 && other.size == 1) bfs(wde, preTrans, n, rs, res)
                  else if(subset.size == 1) bfs(wde, preTrans, n, rs :+ other, res)
                  else if(other.size == 1) bfs(wde, preTrans, n, rs :+ subset, res)
                  else bfs(wde, preTrans, n, rs ++ List(subset, other), res)
                }
              }
            }
          }
        }
      }

      bfs(wde.toList, null, 0, chars :: Nil, Map())
    }

    if(!sstSat) (false, "")
    else loopCS(sstSet)
  }

  def executeZ3(input: String): String = {
    val dir = System.getProperty("user.dir") + "/benchmarks/target"
    val path = dir + "/temp.smt2"

    val directory = new File(dir)
    val file = new File(path)

    if(!directory.exists()) directory.mkdir()
    if (file.exists()) file.createNewFile()


    val pw = new PrintWriter(file)
    pw.write(input)
    pw.close

    val output: String = try {
      ("z3 -smt2 " + path).!!
    } catch {
      case e: Throwable => {
        //e.printStackTrace()
        "unsat"
      }
    }
    //file.delete()
    output
  }
}
