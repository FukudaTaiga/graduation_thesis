package others.matrix

//行列Array(Array(a,b,e),Array(c,d,f))は
//(a,b,e)
//(c,d,f)を表す. Array:rowsize(Array:columnsize)
case class MyMatrix[A](row: Int, column: Int, arr: Vector[Vector[A]]){
  def symmetric(): MyMatrix[A] = {
    val rra = Vector.tabulate(column, row)((i,j) => arr(j)(i))
    new MyMatrix(column, row, rra)
  }

  override def toString(): String = arr.toString
}

case class MyVector[A](val size: Int, val arr: Vector[A]){
  override def toString(): String = arr.toString
}

class BooleanMatrix(row: Int, column: Int, arr: Vector[Vector[Boolean]]) extends MyMatrix[Boolean](row, column, arr){
  val id = Vector.tabulate(row, column)((i,j) => i == j)

  override def symmetric(): BooleanMatrix = {
    val rra = Vector.tabulate(column, row)((i,j) => arr(j)(i))
    new BooleanMatrix(column, row, rra)
  }

  //this -> m' boolAdd m (i,j) = m'(i,j) or m(i,j))
  def boolAdd(m: BooleanMatrix): BooleanMatrix = {
    require(row == m.row && column == m.column)
    val or = Vector.tabulate(row, column)((i,j) => arr(i)(j) || m.arr(i)(j))
    new BooleanMatrix(row, column, or)
  }

  def boolPro(m: BooleanMatrix): BooleanMatrix = {
    require(row == m.row && column == m.column)
    val and = Vector.tabulate(row, column)((i,j) => arr(i)(j) && m.arr(i)(j))
    new BooleanMatrix(row, column, and)
  }

  //this -> m' boolMult m (i,j) = OR(m'(i,k) and m(k,j))
  def boolMult(m: BooleanMatrix): BooleanMatrix = {
    require(column == m.row)
    val and = Vector.tabulate(row, m.column)((i,j) => {
      var b = false
      for(k <- 0 until column)b = b || (arr(i)(k) && m.arr(k)(j))
      b
    })
    new BooleanMatrix(row, m.column, and)
  }

  def exp(n: Int): BooleanMatrix = {
    require(n >= 0)
    if(n == 0)new BooleanMatrix(row,column,id)
    else boolMult(exp(n-1))
  }
}

class BooleanVector(size: Int, arr: Vector[Boolean]) extends MyVector[Boolean](size, arr){
  def boolMult(m: BooleanMatrix): BooleanVector = {
    require(m.column == size)
    val and = Vector.tabulate(m.row)(i => {
      var b = false
      for(k <- 0 until size)b = b || (m.arr(i)(k) && arr(k))
      b
    })
    new BooleanVector(m.row, and)
  }
}

class IntMatrix(row: Int, column: Int, arr: Vector[Vector[Int]]) extends MyMatrix[Int](row, column, arr){
  for(a <- arr){
    require(arr.size == row && a.size == column)
  }

  def add(m: IntMatrix): IntMatrix = {
    require(row == m.row && column == m.column)
    val madd = Vector.tabulate(row, column)((i,j) => arr(i)(j) + m.arr(i)(j))
    new IntMatrix(row, column, madd)
  }

  def pro(m: IntMatrix): IntMatrix = {
    require(column == m.row)
    val mpro = Vector.tabulate(row, m.column)((i,j) => {
      var sum = 0
      for(k <- 0 until column)sum += arr(i)(k)*m.arr(k)(j)
      sum
    })
    new IntMatrix(row, m.column, mpro)
  }

  def concat(v: IntVector): IntMatrix = {
    require(v.size == column)
    new IntMatrix(row + 1, column, arr :+ v.arr)
  }
}

class IntVector(size: Int, arr: Vector[Int]) extends MyVector[Int](size, arr){
  require(size == arr.size)

  val zerov = Vector.tabulate(size)(i => 0)

  def add(v: IntVector): IntVector = {
    require(size == v.size)
    val vadd = Vector.tabulate(size)(i => arr(i) + v.arr(i))
    new IntVector(size, vadd)
  }

  def sub(v: IntVector): IntVector = {
    require(size == v.size)
    val vadd = Vector.tabulate(size)(i => arr(i) - v.arr(i))
    new IntVector(size, vadd)
  }

  def proM(m: IntMatrix): IntVector = {
    require(size == m.column)
    val vpro = Vector.tabulate(m.row)(i => {
      var sum = 0
      for(k <- 0 until m.column)sum += m.arr(i)(k)*arr(k)
      sum
    })
    new IntVector(m.row, vpro)
  }

  def concat(n: Int): IntVector = {
    new IntVector(size + 1, arr :+ n)
  }

  def length(): Int = {
    this.arr.fold(0)((z,x) => z + x)
  }
}
