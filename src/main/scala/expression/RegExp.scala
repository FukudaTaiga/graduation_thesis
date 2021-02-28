package expression.regex

import automata.automata._

trait RegExp{
  def toNFA(): NFA[S, String]
  def isEmpty(): Boolean = {
    this match{
      case EmptyExp => true
      case _ => false
    }
  }
  def size(): Int = {
    this match{
      case EmptyExp => 1
      case EpsExp => 1
      case CharExp(a) => 1
      case AltExp(r1,r2) => r1.size + r2.size + 1
      case ConcatExp(r1,r2) => r1.size + r2.size + 1
      case StarExp(r) => r.size + 1
    }
  }
  override def toString(): String = {
    this match{
      case EmptyExp => "empty"
      case EpsExp => "eps"
      case CharExp(a) => a.toString
      case AltExp(r1,r2) => "(" + r1.toString + "|" + r2.toString + ")"
      case ConcatExp(r1,r2) => r1.toString + r2.toString
      case StarExp(r) => "(" + r.toString + ")" + "*"
    }
  }
  def equal(e: RegExp): Boolean
  def contain(e: RegExp): Boolean
  def reduct(): RegExp
  def rm(): RegExp
}

class S

case class CharExp[A](c: A) extends RegExp {
  val str = c.toString

  def toNFA(): NFA[S,String] = {
    val q0 = new S
    val qf = new S
    val states = Set(q0, qf)
    val transition = Map((q0, Option(str)) -> Set(qf))
    val finalStates = Set(qf)
    new NFA(states, transition, q0, finalStates)
  }
  def equal(e: RegExp) = e match{
    case ch: CharExp[A] => c == ch.c
    case _ => false
  }
  def contain(e: RegExp) = equal(e)
  def reduct(): RegExp = this
  def rm(): RegExp = this
}

case object EmptyExp extends RegExp{
  def toNFA(): NFA[S,String] = {
    val q0 = new S
    val states = Set(q0)
    val transition = Map[(S,Option[String]), Set[S]]()
    val finalStates = Set[S]()

    NFA(states, transition, q0, finalStates)
  }
  def equal(e: RegExp) = e == EmptyExp
  def contain(e: RegExp) = equal(e)
  def reduct(): RegExp = this
  def rm(): RegExp = this
}

case object EpsExp extends RegExp{
  def toNFA(): NFA[S, String] = {
    val q0 = new S
    val qf = new S
    val states = Set(q0, qf)
    val transition = Map[(S, Option[String]), Set[S]]((q0, None: Option[String]) -> Set(qf))
    val finalStates = Set(qf)

    NFA(states, transition, q0, finalStates)
  }
  def equal(e: RegExp) = e == EpsExp
  def contain(e: RegExp) = equal(e)
  def reduct(): RegExp = this
  def rm(): RegExp = this
}

case class ConcatExp(r1: RegExp, r2: RegExp) extends RegExp{
  def toNFA(): NFA[S, String] = {
    val nfa1 = r1.toNFA()
    val nfa2 = r2.toNFA()
    val states = nfa1.states ++ nfa2.states
    val q0 = nfa1.q0
    val q1 = nfa2.q0
    val concat = nfa1.finalStates.map(p => (p, None) -> (nfa1.transition((p, None)) + q1)).toMap
    val transition = nfa1.transition ++ nfa2.transition ++ concat
    val finalstates = nfa2.finalStates

    NFA(states, transition, q0, finalstates)
  }
  def equal(e: RegExp) = {
    val newC = reduct()
    newC match{
      case c: ConcatExp => {
        e.reduct match{
          case ec: ConcatExp => (c.r1 == ec.r1) && (c.r2 == ec.r2)
          case _ => false
        }
      }
      case r => r.equal(e)
    }
  }
  def contain(e: RegExp) = e.reduct == r1 || e.reduct == r2 || r1.contain(e.reduct) || r2.contain(e.reduct)
  def reduct(): RegExp = {
    (r1, r2) match{
      case (EmptyExp, rs2) => EmptyExp
      case (EpsExp, rs2) => rs2.reduct
      case (rs1, EmptyExp) => EmptyExp
      case (rs1, EpsExp) => rs1.reduct
      case (ConcatExp(ls1, ls2), ConcatExp(ls3, ls4)) => ConcatExp(ConcatExp(ConcatExp(ls1.reduct, ls2.reduct), ls3.reduct), ls4.reduct).reduct
      case (rs1, ConcatExp(ls3,ls4)) => ConcatExp(ConcatExp(rs1.reduct, ls3.reduct), ls4.reduct).reduct
      case (rs1, rs2) => ConcatExp(rs1.reduct, rs2.reduct)
    }
  }
  def rm(): RegExp = reduct
}

case class AltExp(r1: RegExp, r2: RegExp) extends RegExp{
  def toNFA(): NFA[S, String] = {
    val nfa1 = r1.toNFA()
    val nfa2 = r2.toNFA()
    val q0 = new S
    val qf = new S
    val states = nfa1.states ++ nfa2.states ++ Set(q0, qf)
    val start = Map((q0, None: Option[String]) -> Set(nfa1.q0, nfa2.q0))
    val goal = (nfa1.finalStates ++ nfa1.finalStates).map(q => {
      val set1 = nfa1.transition((q, None: Option[String]))
      val set2 = nfa2.transition((q, None: Option[String]))
      (q, None: Option[String]) -> (set1 ++ set2 + qf)
    })
    var transition = nfa1.transition ++ nfa2.transition ++ start ++ goal
    val finalStates = nfa1.finalStates ++ nfa2.finalStates

    NFA(states, transition, q0, finalStates)
  }
  def equal(e: RegExp): Boolean = {
    val newA = reduct()
    newA match{
      case a: AltExp => {
        e.reduct match{
          case ea: AltExp => a.r1 == ea.r1 && a.r2 == ea.r2
          case _ => false
        }
      }
      case r => r.equal(e)
    }
  }
  def contain(e: RegExp): Boolean = e.reduct == r1 || e.reduct == r2 || r1.contain(e.reduct) || r2.contain(e.reduct)
  def reduct(): RegExp = {
    (r1, r2) match{
      case (EmptyExp, rs2) => rs2.reduct
      case (rs1, EmptyExp) => rs1.reduct
      case (AltExp(ls1, ls2), AltExp(ls3, ls4)) => AltExp(AltExp(AltExp(ls1.reduct, ls2.reduct), ls3.reduct), ls4.reduct).reduct
      case (rs1, AltExp(ls1, ls2)) => AltExp(AltExp(rs1.reduct, ls1.reduct), ls2.reduct).reduct
      case (rs1, rs2) => AltExp(rs1.reduct, rs2.reduct)
    }
  }
  def rm(): RegExp = {
    val newA = reduct()
    newA match{
      case a: AltExp => {
        if(a.r1.contain(a.r2)) a.r1.rm
        else if(a.r2.contain(a.r1)) a.r2.rm
        else AltExp(r1.rm, r2.rm)
      }
      case r => r.rm
    }
  }
}

case class StarExp(r: RegExp) extends RegExp{
  def toNFA(): NFA[S, String] = {
    val nfa = r.toNFA()
    val states = nfa.states
    val q0 = new S
    val qf = new S
    val finalStates = Set(qf)
    val start = Map((q0, None: Option[String]) -> Set(nfa.q0, qf))
    val goal = nfa.finalStates.map(p => (p, None) -> (nfa.transition((p, None)) + qf)).toMap
    val ret = Map((qf, None) -> Set(q0))
    val transition = nfa.transition ++ start ++ goal ++ ret

    NFA(states, transition, q0, finalStates)
  }
  def equal(e: RegExp): Boolean = {
    r.reduct match{
      case EmptyExp => EpsExp.equal(e)
      case EpsExp => EpsExp.equal(e)
      case s => e match{
        case es: StarExp => es.r.reduct == s
        case _ => false
      }
    }
  }
  def contain(e: RegExp): Boolean = equal(e) || r.contain(e)
  def reduct(): RegExp = {
    r match{
      case EmptyExp => EpsExp
      case EpsExp => EpsExp
      case rs => StarExp(rs.reduct)
    }
  }
  def rm(): RegExp = reduct()
}
