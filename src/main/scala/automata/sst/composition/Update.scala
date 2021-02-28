package automata.sst.composition

object Update {
  def composite[X,B](vars: Set[X], m1: Map[X, List[Either[X,B]]], m2: Map[X, List[Either[X,B]]]): Map[X, List[Either[X,B]]] = {
    vars.map(x => (x, hatHom(m1, m2.withDefaultValue(List(Left(x)))(x)))).toMap
  }

  def hatHom[X,A](m: Map[X, List[Either[X,A]]], list: List[Either[X,A]]): List[Either[X,A]] = {
    list.flatMap(xa => xa match {
      case Left(x) => m.withDefaultValue(List(Left(x)))(x)
      case Right(a) => List(Right(a))
    })
  }

  def identity[X,A](vars: Set[X]): Map[X, List[Either[X,A]]] = {
    vars.map(x => (x, List(Left(x)))).toMap
  }

  def identityShuffle[X](vars: Set[X]): Map[X, List[X]] = {
    vars.map(x => (x, List(x))).toMap
  }
}
