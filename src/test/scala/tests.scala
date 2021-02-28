import org.scalatest._
import automata.automata._
import automata.transducer._
import automata.sst._
import expression._
import others._

class DFATest extends FlatSpec {
  "DFA" should "遷移" in
  {
    val dfa = new DFA(Set(0,1,2),
      Map(
        (0,'0')->2,
        (0,'1')->0,
        (1,'0')->0,
        (1,'1')->1,
        (2,'0')->2,
        (2,'1')->1),
      0,Set(1))

    assert(dfa.trans(0,List('0','1')) == 1)
    assert(dfa.accept(List('0','1')))
    assert(!dfa.accept(List('1', '1', '0')))
  }
}

class NFATest extends FlatSpec {
  val trans1 =
    Map(
      (0,None)->Set(1),
      (1,Some('0'))->Set(0),
      (1,None)->Set(0))
  val nfa1 = new NFA(Set(0,1),trans1,0,Set(1))

  val trans2 =
    Map(
      (0,Some('0'))->Set(0),
      (0,None)->Set(1),
      (1,Some('1'))->Set(1),
      (1,None)->Set(2),
      (2,Some('2'))->Set(2))
  val nfa2 = new NFA(Set(0,1,2),trans2,0,Set(2))
  val nfa3 = NFA2(Set(0,1,2),trans2,Set(0),Set(2))

  "NFA" should "ε-closure" in
  {
    assert(nfa1.eclosure(Set(0)) == Set(0,1))
    assert(nfa2.eclosure(Set(0)) == Set(0,1,2))
    assert(nfa3.eclosure(Set(0)) == Set(0,1,2))
  }

  "NFA" should "transition" in
  {
    assert(nfa2.trans(0, List('1')) == Set(1,2))
    assert(nfa3.transSet(Set(0), List('1')) == Set(1,2))
  }

  "NFA" should "accept" in
  {
    assert(nfa2.accept(List('0','1','1')))
    assert(nfa2.accept(List('0','1','1','2')))
    assert(!nfa2.accept(List('0','1','0')))

    assert(nfa3.accept(List('0','1','1')))
    assert(nfa3.accept(List('0','1','1','2')))
    assert(!nfa3.accept(List('0','1','0')))
  }

  "NFA" should "サブセット構成" in
  {
    val dfa = nfa2.toDFA()
    assert(dfa.states == Set(Set(0,1,2),Set(1,2),Set(2),Set()))
    assert(dfa.accept(List('0','0','2')))
    assert(!dfa.accept(List('0','0','2','1')))
    assert(dfa.transition(Set(0,1,2),'0')== Set(0,1,2))
    assert(dfa.transition(Set(0,1,2),'1')== Set(1,2))
    assert(dfa.transition(Set(0,1,2),'2')== Set(2))
    assert(dfa.transition(Set(1,2),'0')== Set())
    assert(dfa.transition(Set(1,2),'1')== Set(1,2))
    assert(dfa.transition(Set(1,2),'2')== Set(2))
    assert(dfa.transition(Set(2),'0')== Set())
    assert(dfa.transition(Set(2),'1')== Set())
    assert(dfa.transition(Set(2),'2')== Set(2))
    assert(dfa.transition(Set(),'0')== Set())
    assert(dfa.transition(Set(),'1')== Set())
    assert(dfa.transition(Set(),'2')== Set())

    val dfa1 = nfa3.toDFA()
    assert(dfa1.states == Set(Set(0,1,2),Set(1,2),Set(2),Set()))
    assert(dfa1.accept(List('0','0','2')))
    assert(!dfa1.accept(List('0','0','2','1')))
    assert(dfa1.transition(Set(0,1,2),'0')== Set(0,1,2))
    assert(dfa1.transition(Set(0,1,2),'1')== Set(1,2))
    assert(dfa1.transition(Set(0,1,2),'2')== Set(2))
    assert(dfa1.transition(Set(1,2),'0')== Set())
    assert(dfa1.transition(Set(1,2),'1')== Set(1,2))
    assert(dfa1.transition(Set(1,2),'2')== Set(2))
    assert(dfa1.transition(Set(2),'0')== Set())
    assert(dfa1.transition(Set(2),'1')== Set())
    assert(dfa1.transition(Set(2),'2')== Set(2))
    assert(dfa1.transition(Set(),'0')== Set())
    assert(dfa1.transition(Set(),'1')== Set())
    assert(dfa1.transition(Set(),'2')== Set())
  }
}

  class RegFATest extends FlatSpec {
    val states = Set("1","2","3")
    val alpha = Set(0,1)

    val trans1 = Map(("1",0) -> "2", ("2",0) -> "3", ("3",1) -> "3")
    val trans2 = Map(("1",0) -> "1")

    val dfa1 = new DFA(states, trans1, "1", Set("3"))
    val dfa2 = new DFA(states, trans2, "1", Set("3"))
    val dfa3 = new DFA(states, trans1, "1", Set())
    val e1 = dfa1.toGFA.toReg()
    val e2 = dfa2.toGFA.toReg()
    val e3 = dfa3.toGFA.toReg()

    val nfa1 = e1.toNFA()
    val nfa2 = e2.toNFA()

    "FA->Reg" should "DFAtoReg" in {
      assert(e1.toString == "00(1)*")
      assert(e2.toString == "empty")
      assert(e3.toString == "empty")
    }

    "Reg->FA" should "RegtoNFA" in {
      assert(nfa1.accept(List("0", "0", "1")))
      assert(nfa1.accept(List("0","0","1","1","1")))
      assert(!nfa1.accept(List("0","0","1","0")))
    }
  }

  class TransducerTest extends FlatSpec {
    val m =
      Map[(String,List[Int]),Set[(String,List[Int])]](
        ("p",List(1))->Set(("q",List(1))),
        ("p",List(0))->Set(("p",List(0))),
        ("q",List(1))->Set(("q",Nil)),
        ("q",List(0))->Set(("p",List(0)))
      )

    val n = Map[(String,List[Int]),Set[(String,List[Int])]](
      ("p",List(0))->Set(("q",List(0))),
      ("p",List(1))->Set(("p",List(1))),
      ("q",List(0))->Set(("q",Nil)),
      ("q",List(1))->Set(("p",List(1)))
    )

    val states = Set("p","q")
    val alpha = (Set(0,1), Set(0,1))
    val qs = "p"
    val fs = Set("p","q")
    //tは１の列を一つの１に、sは０で同様の動作をするTransducer
    val t = new NTransducer(states, m, qs, fs)
    val s = new NTransducer(states, n, qs, fs)
    val bt = t.toBasic
    val bs = s.toBasic
    val comp = bt.comp(bs)

    "Transducer" should "worktest" in {
      val accept = bt.accept(List(0,0,1,1,0,1,1,1))._1
      val output = bt.accept(List(0,0,1,1,0,1,1,1))._2.toString
      assert((accept, output) == (true, "00101"))
    }

    "Transducer" should "composition" in {
      val accept = comp.accept(List(0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,1,1,1,0))._1
      val output = comp.accept(List(0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,1,1,1,0))._2.toString
      assert((accept, output) == (true,"0101010"))
    }
  }

  class SSTTest extends FlatSpec {
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
    val finalMap1 = Map(1 -> List[Either[Char,Char]](Left('x'), Left('y')))
    //入力とその反転を連結したものを返す
    val sst = SST(states1, variables1, delta1, eta1, q01, finalMap1)

    "SST" should "tests" in {
      assert(sst.accept("abaab") == (false, ""))
      assert(sst.accept("abaab$") == (true, "abaabbaaba"))
    }
  }
