package others.execute

import java.io.{File, PrintWriter}

import formula.presburger._

case class Execute(
  ps: Set[Presburger],
  bVars: Set[Var],
  dVars: Set[Var],
  qVars: Set[Var],
  rVars: Set[Var],
  sVars: Set[Var],
  nVars: Set[Var]
){
  def z3Input(option: Boolean, isSub: Boolean): String = {
    def concatWithAnd(ls: List[String]): String = {
      ls match{
        case Nil => ""
        case s::Nil => "\n" + s
        case r::rs => "(and " + concatWithAnd(rs) + "\n" + r + ") "
      }
    }

    val bDec: String = bVars.map(v => "(declare-const " + v.toString + " Int) \n").mkString
    val dDec: String = dVars.map(v => "(declare-const " + v.toString + " Int) \n").mkString
    val qDec: String = qVars.map(v => "(declare-const " + v.toString + " Int) \n").mkString
    val rDec: String = rVars.map(v => "(declare-const " + v.toString + " Int) \n").mkString
    val sDec: String = sVars.map(v => "(declare-const " + v.toString + " Int) \n").mkString
    val nDec: String = nVars.map(v => "(declare-const " + v.toString + " Int) \n").mkString

    val dEx = dVars.map(v => "(" + v.toString + " Int) \n").mkString
    val qEx = qVars.map(v => "(" + v.toString + " Int) \n").mkString
    val rEx = rVars.map(v => "(" + v.toString + " Int) \n").mkString
    val sEx = sVars.map(v => "(" + v.toString + " Int) \n").mkString
    val nEx = nVars.map(v => "(" + v.toString + " Int) \n").mkString

    val bcond = bVars.map(v => "(" + "<= 0 " + v.toString + ")")
    // val dcond = dVars.map(v => "(" + "<= 0 " + v.toString + ")")
    // val qcond = qVars.map(v => "(" + "<= -1 " + v.toString + ")")
    // val ncond = nVars.map(v => "(" + "<= 0 " + v.toString + ")")

    val as = "(assert "
    val rb = ") \n"

    val cond = bcond.map(str => as + str + rb).mkString
    // val cond0 = {dcond.map(str => as + str + rb).mkString +
    //             qcond.map(str => as + str + rb).mkString +
    //             ncond.map(str => as + str + rb).mkString}

    val prop0 = ps.map(pf => "(assert(" + pf.mkz3String + ")) \n \n").mkString
    val exists = "(assert(exists ( \n" + dEx + qEx + rEx + sEx + nEx + ") "
    val ls =  ps.map(pf => "(" + pf.mkz3String + ") \n").toList
    val prop1 = exists + concatWithAnd(ls) + "))"

    val check = "(check-sat) \n" + "(get-model) \n"

    if(option && isSub){
      val getDeclare = bDec + dDec + qDec + rDec + sDec + nDec
      getDeclare + "\n" + prop0 + "\n" + check
    }
    else if(!option && isSub){
      val getDeclare = bDec
      getDeclare + "\n" + prop1 + "\n" + check
    }
    else if(option && !isSub){
      val getDeclare = bDec + dDec + qDec + rDec + sDec + nDec
      getDeclare + "\n" + cond + "\n" + prop0 + "\n" + check
    }
    else{
      val getDeclare = bDec
      getDeclare + "\n" + cond + prop1 + "\n" + check
    }
  }

  def mkFile(filename: String, option: Boolean, isSub: Boolean): Unit = {
    val dirpath = System.getProperty("user.dir") + "/benchmark"

    val dir = new File(dirpath)
    if(dir.exists){}
    else {
      dir.mkdir()
      println(dirpath + "is made")
    }

    val path = dir + "/" + filename + ".smt2"

    val file = new File(path)

    if(file.exists)file.createNewFile

    val pw = new PrintWriter(file)
    pw.write(z3Input(option, isSub))
    pw.close()
  }
}
