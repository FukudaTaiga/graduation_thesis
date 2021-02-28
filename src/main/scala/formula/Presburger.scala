package formula.presburger

import others.matrix._

trait Integers {
  def varSet(): Set[Var]
  def reduct(): Integers
  def toString(): String
  def mkz3String(): String
}

trait Term extends Integers {
  def varSet(): Set[Var]
  def reduct2(): Term
  def mkz3String(): String
}

case class Const(n: Int) extends Integers with Term {
  override def varSet = Set()
  override def reduct = if(n == 0) Zero else if(n == 1) One else this
  override def reduct2 = if(n == 0) Zero else if(n == 1) One else this
  override def toString = n.toString
  override def mkz3String = n.toString
}
object Zero extends Term {
  override def varSet = Set()
  override def reduct = this
  override def reduct2 = this
  override def toString = "0"
  override def mkz3String = "0"
}
object One extends Term {
  override def varSet = Set()
  override def reduct = this
  override def reduct2 = this
  override def toString = "1"
  override def mkz3String = "1"
}
case class Var(name: String, idx: Int, sign: Boolean = true) extends Integers with Term {
  override def varSet = Set(this)
  override def reduct = this
  override def reduct2 = this
  override def toString = name + "_" + idx
  override def mkz3String = name + "_" + idx
}
//i + j
case class Add(i: Integers, j: Integers) extends Integers {
  override def varSet = i.varSet ++ j.varSet
  override def reduct = {
    (i, j) match {
      case (Const(0), k) => k.reduct
      case (k, Const(0)) => k.reduct
      case (Const(n), Const(m)) => Const(n + m).reduct
      case _ => Add(i.reduct, j.reduct)
    }
  }
  override def toString = "(" + i.toString + "+" + j.toString + ")"
  override def mkz3String = "(+ " + i.mkz3String + " " + j.mkz3String + ")"
}
case class AddList(list: List[Term]) extends Integers {
  override def varSet = list.flatMap(t => t.varSet).toSet
  override def reduct = AddList(list.collect{ case t if t.reduct2 != Zero => t.reduct2 })
  override def toString = list.map(t => t.toString).foldLeft("0")((sum, s) => "(" + sum + " + " + s + ")")
  override def mkz3String = if(list.isEmpty) "0" else list.tail.map(t => t.mkz3String).foldLeft(list.head.mkz3String)((sum, s) => "(+ " + sum + " " + s + ")")
}
//i-j
case class Sub(i: Integers, j: Integers) extends Integers {
  override def varSet = i.varSet ++ j.varSet
  override def reduct: Integers = {
    (i, j) match {
      case (k, Const(0)) => k.reduct
      case (Const(n), Const(m)) => Const(n - m).reduct
      case _ => Sub(i.reduct, j.reduct)
    }
  }
  override def toString = "(" + i.toString + "-" + j.toString + ")"
  override def mkz3String = "(- " + i.mkz3String + " " + j.mkz3String + ")"
}
//i*j
case class Mult(i: Const, v: Var) extends Integers with Term {
  override def varSet = Set(v)
  override def reduct: Integers = {
    i.reduct match{
      case Const(1) => v
      case Const(0) => Zero
      case _ => this
    }
  }
  override def reduct2 = {
    i.reduct match{
      case Const(1) => v
      case Const(0) => Zero
      case _ => this
    }
  }
  override def toString = "(" + i.toString + "*" + v.toString + ")"
  override def mkz3String = "(* " + i.mkz3String + " " + v.mkz3String + ")"
}


trait Presburger {
  def varSet: Set[Var]
  def fv(): Set[Var]
  def reduct(): Presburger
  def toString(): String
  //reductするとtrue・false・othersになるので, or (true) (= x y)のようにはならない.
  def mkz3String(): String
}

case object Top extends Presburger {
  override def varSet = Set()
  override def fv = Set()
  override def reduct = this
  override def toString = "true"
  override def mkz3String() = "true"
}
case object Bottom extends Presburger {
  override def varSet = Set()
  override def fv = Set()
  override def reduct = this
  override def toString = "false"
  override def mkz3String() = "false"
}
case class Eq(i: Integers, j: Integers) extends Presburger {
  override def varSet = i.varSet ++ j.varSet
  override def fv = i.varSet ++ j.varSet
  override def reduct = Eq(i.reduct, j.reduct)
  override def toString = "(" + i.toString + "=" + j.toString + ")"
  override def mkz3String() = "(= " + i.mkz3String + " " + j.mkz3String + ")"
}
// i < j
case class Lt(i: Integers, j: Integers) extends Presburger {
  override def varSet = i.varSet ++ j.varSet
  override def fv = i.varSet ++ j.varSet
  override def reduct = Lt(i.reduct, j.reduct)
  override def toString = "(" + i.toString + "<" + j.toString + ")"
  override def mkz3String() = "(< " + i.mkz3String + " " + j.mkz3String + ")"
}
case class Leq(i: Integers, j: Integers) extends Presburger {
  override def varSet = i.varSet ++ j.varSet
  override def fv = i.varSet ++ j.varSet
  override def reduct = Leq(i.reduct, j.reduct)
  override def toString = "(" + i.toString + "<=" + j.toString + ")"
  override def mkz3String() = "(<= " + i.mkz3String + " " + j.mkz3String + ")"
}
case class Or(f: Presburger, g: Presburger) extends Presburger {
  override def varSet = f.varSet ++ g.varSet
  override def fv = f.fv ++ g.fv
  override def reduct = {
    (f.reduct, g.reduct) match{
      case (Top, _) => Top
      case (_, Top) => Top
      case (Bottom, _) => g.reduct
      case (_, Bottom) => f.reduct
      case (_, _) => Or(f.reduct, g.reduct)
    }
  }
  override def toString = "(" + f.toString + "|" + g.toString + ")"
  override def mkz3String() = "(or " + f.mkz3String + " " + g.mkz3String + ")"
}
case class OrList(list: List[Presburger]) extends Presburger {
  override def varSet = list.flatMap(p => p.varSet).toSet
  override def fv = list.flatMap(p => p.fv).toSet
  override def reduct = if(list.map(p => p.reduct).contains(Top)) Top else OrList(list.collect{ case b if b.reduct != Bottom => b.reduct})
  override def toString = list.map(p => p.toString).foldLeft("false")((bool, s) => "(" + bool + "|" + s + ")")
  override def mkz3String = if(list.isEmpty) "true" else list.tail.map(p => p.mkz3String).foldLeft(list.head.mkz3String)((bool, s) => "(or " + bool + " " + s + ")")
}
case class And(f: Presburger, g: Presburger) extends Presburger {
  override def varSet = f.varSet ++ g.varSet
  override def fv = f.fv ++ g.fv
  override def reduct = {
    (f.reduct, g.reduct) match{
      case (Top, _) => g.reduct
      case (_, Top) => f.reduct
      case (Bottom, _) => Bottom
      case (_, Bottom) => Bottom
      case (_, _) => And(f.reduct, g.reduct)
    }
  }
  override def toString = "(" + f.toString + "&" + g.toString + ")"
  override def mkz3String() = "(and " + f.mkz3String + " " + g.mkz3String + ")"
}
case class AndList(list: List[Presburger]) extends Presburger {
  override def varSet = list.flatMap(p => p.varSet).toSet
  override def fv = list.flatMap(p => p.fv).toSet
  override def reduct = if(list.map(p => p.reduct).contains(Bottom)) Bottom else AndList(list.collect{ case b if b.reduct != Top => b.reduct})
  override def toString = list.map(p => p.toString).foldLeft("true")((bool, s) => "(" + bool + "&" + s + ")")
  override def mkz3String = if(list.isEmpty) "true" else list.tail.map(p => p.mkz3String).foldLeft(list.head.mkz3String)((bool, s) => "(and " + bool + " " + s + ")")
}
case class Exists(vs: Set[Var], f: Presburger) extends Presburger {
  override def varSet = f.varSet
  override def fv = f.fv diff vs
  override def reduct = Exists(vs, f.reduct)
  override def toString = {
    val str = vs.fold("")((str, v) => str + v.toString + " ")
    "exist(" + str + "). " + f.toString
  }
  override def mkz3String() = f.mkz3String
}
case class Not(f: Presburger) extends Presburger {
  override def varSet = f.varSet
  override def fv = f.fv
  override def reduct = {
    f match{
      case Top => Bottom
      case Bottom => Top
      case ng: Not => ng.f.reduct
      case formula: Or => And(Not(formula.f.reduct), Not(formula.g.reduct))
      case formula: And => Or(Not(formula.f.reduct), Not(formula.g.reduct))
      case _ => Not(f.reduct)
    }
  }
  override def toString = "¬ (" + f.toString + ")"
  override def mkz3String() = "(not " + f.mkz3String + ")"
}
