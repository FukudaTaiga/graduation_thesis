package builder

import formula.atomic.{IntegerEquation, StrInRe, WordEquation}
import formula.integer._
import formula.re._
import formula.str._
import formula.{Conjunction, Disjunction, Negation, ReturnBoolean}

case class FormulaBuilder(source: String) {

  def output: (ReturnBoolean, Boolean) = {
    //input Stringをある程度のまとまりにしたListからReturnBooleanを構成して返す.
    def loop(
      tokens: List[String], p: ReturnBoolean, strV: Set[String], intV: Set[String], checkSat: Boolean, getModel: Boolean
    ): (ReturnBoolean, Set[String], Set[String], Boolean, Boolean) = {
      //(0 何か1 ... )n . 1で何がdeclareされているか判断し, それぞれの関数に投げる.
      tokens(1) match {
        case "check-sat" => {
          val temp = parseCheckSat(tokens)
          if (temp.isEmpty)
            (p, strV, intV, true, getModel)
          else if(temp.length > 1 && temp(1).equals("get-model"))  //(0 get-model1 )2 ...
            (p, strV, intV, true, true)
          else
            (p, strV, intV, true, false)
        }
        case "declare-const" => {
          val (temp, strV1, intV1) = parseDeclareConst(tokens, strV, intV)
          loop(temp, p, strV1, intV1, checkSat, getModel)
        }
        case "declare-fun" => {
          val (temp, strV1, intV1) = parseDeclareFun(tokens, strV, intV)
          loop(temp, p, strV1, intV1, checkSat, getModel)
        }
        case "assert" => {
          val (temp, formula) = parseAssert(tokens, strV, intV)
          if (p == null)
            loop(temp, formula, strV, intV, checkSat, getModel)
          else
            loop(temp, Conjunction(p, formula), strV, intV, checkSat, getModel)
        }
      }
    }

    val (res, _, strV, _, getModel) = loop(getTokens(source), null, Set[String](), Set[String](), false, false)
    (res, getModel)
  }

  val diseq = Map(
    "<" -> 2,
    ">=" -> -2,
    ">" -> 3,
    "<=" -> -3
  )

  //input Stringをある程度のまとまりにしたListに変換.
  def getTokens(str: String): List[String] = {
    val source = str.replaceAll("\\(", " ( ").replaceAll("\\)", " ) ").toList

    def loop(quote: Boolean, source: List[Char], temp: String, res: List[String]): List[String] = {
      source match {
        case Nil => res ::: List(temp)
        case x :: xs if !quote && x == '\"' => loop(true, xs, "" + x, res) //quateでくくりはじめ.
        case x :: xs if quote && x == '\"' => loop(false, xs, "", res ::: List(temp + x)) //quate終わり.
        case x :: xs if quote => loop(quote, xs, temp + x, res) //quateで括られている部分をtempに保存していく.
        case x :: xs if x.isWhitespace => loop(quote, xs, "", res ::: List(temp)) //空白にmatchしたらそこまでをひとまとまりに.
        case x :: xs => loop(quote, xs, temp + x, res) //tempに保存.
      }
    }

    loop(false, source, "", List()).filterNot(_.isEmpty)
  }

  //(tokens, strVs, intVs)を返す.
  def parseDeclareFun(tokens: List[String], strV: Set[String], intV: Set[String]): (List[String], Set[String], Set[String]) = {
    tokens(5) match {
      case "Int" => (tokens.drop(7), strV, intV + tokens(2)) //(0 declare-fun1 x2 (3  )4 Int5 )6 7個は切り捨てて次に行く.
      case "String" => (tokens.drop(7), strV + tokens(2), intV) // ( declare-fun x (  ) String )
    }
  }

  //(tokens, strVs, intVs)を返す.
  def parseDeclareConst(tokens: List[String], strV: Set[String], intV: Set[String]): (List[String], Set[String], Set[String]) = {
    tokens(3) match {
      case "Int" => (tokens.drop(5), strV, intV + tokens(2)) //(0 declare-const1 x2  Int3 )4 5個は切り捨てて次に行く.
      case "String" => (tokens.drop(5), strV + tokens(2), intV) // ( declare-const x  String )
    }
  }

  //assertがきたことを検知.
  def parseAssert(tokens: List[String], strV: Set[String], intV: Set[String]): (List[String], ReturnBoolean) = {
    //(0 assert1 ... )n
    val (temp, formula) = parseFormula(tokens.drop(2), strV, intV) //2個は切り捨ててformulaを取りに行く.
    (temp.drop(1), formula) //)nを切り捨てて次に行く.
  }

  def parseFormula(tokens: List[String], strV: Set[String], intV: Set[String]): (List[String], ReturnBoolean) = {
    tokens(1) match { //assert以下は(0 演算子1 ...)n-1 )n の形.
      case "=" => { //( = ()  ()  )
        //intのequationか. countは閉じられていない(の数.
        def intEq(queue: List[String], count: Int): Boolean = {
          if (count == 0)
            false
          else {
            queue match {
              case x :: xs if x.equals("(") => intEq(xs, count + 1)
              case x :: xs if x.equals(")") => intEq(xs, count - 1)
              case x :: _ if (x.head == '-' || x.head == '+' || x.head.isDigit) && (x.drop(1) forall Character.isDigit) => true
              case x :: _ if x.equals("str.len") => true
              case x :: _ if intV.contains(x) => true
              case x :: _ if strV.contains(x) => false
              case x :: _ if x.startsWith("str.") => false
              case _ :: xs => intEq(xs, count)
            }
          }
        }

        if (intEq(tokens.drop(2), 1)) { //(0 =1 n1 n2  )
          val (temp1, int1) = parseInt(tokens.drop(2), strV, intV)  //tokens.drop(2) => n1 n2 ), temp1 => n2 )
          val (temp2, int2) = parseInt(temp1, strV, intV)  //temp2 => )
          (temp2.drop(1), IntegerEquation(int1, int2, 1))  //)を一つ落として次に.
        }
        else { //( =  x "aba" )
          val (temp1, str1) = parseString(tokens.drop(2), strV, intV)
          val (temp2, str2) = parseString(temp1, strV, intV)
          (str1, str2) match {
            case (x: StrV, _) => (temp2.drop(1), WordEquation(x, str2))
            case (_, y: StrV) => (temp2.drop(1), WordEquation(y, str1))
            case (_, _) => (temp2.drop(1), IntegerEquation(IntC(0), IntC(0), -1)) //
          }
        }
      }
      //確実にIntegerEq
      case "<" | "<=" | ">" | ">=" => { //( < n1 n2 )
        val (temp1, int1) = parseInt(tokens.drop(2), strV, intV)  //tokens.drop(2) => n1 n2 ), temp1 => n2 )
        val (temp2, int2) = parseInt(temp1, strV, intV)  //temp2 => )
        (temp2.drop(1), IntegerEquation(int1, int2, diseq(tokens(1))))  //)を一つ落として次に.
      }
      //regularの条件
      case "str.in.re" => { // (0 str.in.re1 x2 (...) )
        val x = StrV(tokens(2))
        val (temp, re) = parseRegular(tokens.drop(3), strV, intV)  //tokens.drop(3) => (...) ), temp => )
        (temp.drop(1), StrInRe(x, re, false))
      }
      //
      case "not" => { // (0 not1 (...) )
        val (temp, formula) = parseFormula(tokens.drop(2), strV, intV)
        //tokens.drop(2) => (...) ), temp => ), formula => (...)の部分
        (temp.drop(1), Negation(formula))
      }

      case "and" => { // ( and () () )
        val (temp1, f1) = parseFormula(tokens.drop(2), strV, intV)
        val (temp2, f2) = parseFormula(temp1, strV, intV)
        (temp2.drop(1), Conjunction(f1, f2))
      }

      case "or" => { // ( or () () )
        val (temp1, f1) = parseFormula(tokens.drop(2), strV, intV)
        val (temp2, f2) = parseFormula(temp1, strV, intV)
        (temp2.drop(1), Disjunction(f1, f2))
      }
    }
  }

  //これが呼ばれるときは次がIntは確定.
  def parseInt(tokens: List[String], strV: Set[String], intV: Set[String]): (List[String], ReturnInteger) = {
    //1 ここでの-, +は二項演算子ではなく正負を表すもの.
    if ((tokens(0).charAt(0) == '-' || tokens(0).charAt(0) == '+' || tokens(0).charAt(0).isDigit)
      && (tokens(0).drop(1) forall Character.isDigit)){
      (tokens.drop(1), IntC(tokens(0).toInt))
    }
    //a
    else if (!tokens(0).equals("(")) {
      (tokens.drop(1), IntV(tokens(0)))
    }
    //(0 str.len1  x2 )3
    else if (tokens(1).equals("str.len")) {
      (tokens.drop(4), StrLen(StrV(tokens(2))))
    }
    //(0 +1 n2 ( str.len x ) )
    else {
      val operator = tokens(1)
      //tokens.drop(2) => n ( str.len x ) )
      val (temp1, operand1) = parseInt(tokens.drop(2), strV, intV)  //operand1 => n, temp1 => ( str.len x ) )
      val (temp2, operand2) = parseInt(temp1, strV, intV)  //operand2 => ( str.len x ), temp2 => )
      (temp2.drop(1), Operation(operand1, operand2, operator))
    }
  }

  def parseString(tokens: List[String], strV: Set[String], intV: Set[String]): (List[String], ReturnString) = {
    if (!tokens(0).equals("(") && tokens(0).charAt(0) != '\"') {
      //x
      (tokens.drop(1), StrV(tokens(0)))
    }
    else if (!tokens(0).equals("(")) {
      //"abc"
      (tokens.drop(1), StrConcat(List(Right(tokens(0).drop(1).dropRight(1)))))
    }
    else {
      tokens(1) match {
        case "str.at" => { // ( str.at  x  1 )
          (tokens.drop(5), StrAt(StrV(tokens(2)), tokens(3).toInt))
        }
        case "str.++" => { // ( str.++ x "abc" x )
          def loop(temp: List[String], res: List[Either[StrV, String]]): (List[String], List[Either[StrV, String]]) = {
            if (temp(0).equals(")"))
              (temp.drop(1), res)
            else if (temp(0).charAt(0) == '\"') { //"abc"
              loop(temp.drop(1), res ::: List(Right(temp(0).drop(1).dropRight(1))))
            }
            else { // x
              loop(temp.drop(1), res ::: List(Left(StrV(temp(0)))))
            }
          }

          val (tokens1, list) = loop(tokens.drop(2), List())
          (tokens1, StrConcat(list))
        }
        case "str.replace" => { //( str.replace x "pattern" "replacement" )
          (tokens.drop(6), StrReplace(StrV(tokens(2)), tokens(3).drop(1).dropRight(1), tokens(4).drop(1).dropRight(1)))
        }
        case "str.replaceall" => { //( str.replaceall x "pattern" "replacement" )
          (tokens.drop(6), StrReplaceAll(StrV(tokens(2)), tokens(3).drop(1).dropRight(1), tokens(4).drop(1).dropRight(1)))
        }
        case "str.reverse" => { //( str.reverse x )
          (tokens.drop(4), StrReverse(StrV(tokens(2))))
        }
        case "str.insert" => { // ( str.insert x 1 "abab" )
          (tokens.drop(6), StrInsert(StrV(tokens(2)), tokens(3).toInt, tokens(4).drop(1).dropRight(1)))
        }
        case "str.substr" => {
          if (tokens(4).equals(")")) // ( str.substr x begin )
            (tokens.drop(5), StrSubstr(StrV(tokens(2)), tokens(3).toInt))
          else // ( str.substr x begin count )
            (tokens.drop(6), StrSubstrcount(StrV(tokens(2)), tokens(3).toInt, tokens(4).toInt))
        }
      }
    }
  }

  def parseRegular(tokens: List[String], strV: Set[String], intV: Set[String]): (List[String], ReturnRe) = {
    if (tokens(0).equals("re.allchar")) { // re,allchar
      return (tokens.drop(1), ReAllchar())
    }
    tokens(1) match {
      case "str.to.re" => { //( str.to.re  "abc" )
        (tokens.drop(4), StrToRe(tokens(2).drop(1).dropRight(1)))
      }
      case "re.*" => { // ( re.* ( str.to.re "a" ) )
        val (temp, re) = parseRegular(tokens.drop(2), strV, intV)
        (temp.drop(1), ReStar(re))
      }
      case "re.+" => { // ( re.+ ( str.to.re "a" ) )
        val (temp, re) = parseRegular(tokens.drop(2), strV, intV)
        (temp.drop(1), ReConcat(ReStar(re), re))
      }
      case "re.++" => { // ( re.++ ( str.to.re "a" ) ( str.to.re "b" ) (...) (...) )
        def loop(temp: List[String], re: ReturnRe): (List[String], ReturnRe) = {
          if (temp(0).equals(")"))
            (temp.drop(1), re)
          else {
            val (temp1, re1) = parseRegular(temp, strV, intV)
            loop(temp1, ReConcat(re, re1))
          }
        }

        val (temp0, re0) = parseRegular(tokens.drop(2), strV, intV)
        loop(temp0, re0)
      }
      case "re.union" => { // ( re.union ( str.to.re "a" ) ( str.to.re "b" ) (...) (...) ); one or more
        def loop(temp: List[String], re: ReturnRe): (List[String], ReturnRe) = {
          if (temp(0).equals(")"))
            (temp.drop(1), re)
          else {
            val (temp1, re1) = parseRegular(temp, strV, intV)
            loop(temp1, ReUnion(re, re1))
          }
        }

        val (temp0, re0) = parseRegular(tokens.drop(2), strV, intV)
        loop(temp0, re0)
      }
      case "re.range" => {
        // ( re.range "a" "b" )
        (tokens.drop(5), ReRange(tokens(2).charAt(1), tokens(3).charAt(1)))
      }
    }
  }

  def parseCheckSat(tokens: List[String]): List[String] = tokens.drop(3) //( check-sat )

  def parseGetModel(tokens: List[String]): List[String] = tokens.drop(3) //( get-model )

}
