import scala.util.parsing.combinator._
import java.io.FileReader

// TODO:
// 1. parser written but faulty (find.imp not working for example)
// 2. translate Write statement into guarded commands
// 3. write replace function
// 4. write havocVars function
// 5. translate guarded commands into verification condition

object VCGen {

  /* Arithmetic expressions. */
  trait ArithExp

  case class Num(value: Int) extends ArithExp
  case class Var(name: String) extends ArithExp
  case class Read(name: String, ind: ArithExp) extends ArithExp
  case class Add(left: ArithExp, right: ArithExp) extends ArithExp
  case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
  case class Div(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
  case class Parens(a: ArithExp) extends ArithExp


  /* Comparisons of arithmetic expressions. */
  type Comparison = Product3[ArithExp, String, ArithExp]


  /* Boolean expressions. */
  trait BoolExp

  case class BCmp(cmp: Comparison) extends BoolExp
  case class BNot(b: BoolExp) extends BoolExp
  case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BParens(b: BoolExp) extends BoolExp


  /* Statements and blocks. */
  trait Statement
  type Block = List[Statement]

  case class Assign(x: String, value: ArithExp) extends Statement
  case class Write(x: String, ind: ArithExp, value: ArithExp) extends Statement
  case class ParAssign(x1: String, x2: String, value1: ArithExp, value2: ArithExp) extends Statement
  case class If(cond: BoolExp, th: Block, el: Block) extends Statement
  case class While(cond: BoolExp, inv: List[Assertion], body: Block) extends Statement


  /* Assertions. */
  trait Assertion
  type Preconditions = List[Assertion]
  type Postconditions = List[Assertion]

  case class ACmp(cmp: Comparison) extends Assertion
  case class ANot(a: Assertion) extends Assertion
  case class ADisj(left: Assertion, right: Assertion) extends Assertion
  case class AConj(left: Assertion, right: Assertion) extends Assertion
  case class AImplies(left: Assertion, right: Assertion) extends Assertion
  case class AForall(x: String, a: Assertion) extends Assertion
  case class AExists(x: String, a: Assertion) extends Assertion
  case class AParens(a: Assertion) extends Assertion

  /* Complete programs. */
  type Program = Product4[String, Preconditions, Postconditions, Block]


  /* Loop-free guarded commands.*/
  trait GuardedCommand

  case class Assume(a: Assertion) extends GuardedCommand
  case class Assert(b: Assertion) extends GuardedCommand
  case class Havoc(x: String) extends GuardedCommand
  case class Concat(c1: GuardedCommand, c2: GuardedCommand) extends GuardedCommand
  case class Rect(c1: GuardedCommand, c2: GuardedCommand) extends GuardedCommand

  object ImpParser extends RegexParsers {
    /* General helpers. */
    def pvar  : Parser[String] = "\\p{Alpha}(\\p{Alnum}|_)*".r

    /* Parsing for ArithExp. */
    def num   : Parser[ArithExp] = "-?\\d+".r ^^ (s => Num(s.toInt))
    def atom  : Parser[ArithExp] =
      "(" ~> aexp <~ ")" |
      pvar ~ ("[" ~> aexp <~ "]") ^^ {case v ~ i => Read(v, i)} |
      num | pvar ^^ { Var(_) } |
      "-" ~> atom ^^ { Sub(Num(0), _) }
    def factor: Parser[ArithExp] =
      atom ~ rep("*" ~ atom | "/" ~ atom | "%" ~ atom) ^^ {
        case left ~ list => (left /: list) {
          case (left, "*" ~ right) => Mul(left, right)
          case (left, "/" ~ right) => Div(left, right)
          case (left, "%" ~ right) => Mod(left, right)
        }
      }
    def term  : Parser[ArithExp] =
      factor ~ rep("+" ~ factor | "-" ~ factor) ^^ {
        case left ~ list => (left /: list) {
          case (left, "+" ~ right) => Add(left, right)
          case (left, "-" ~ right) => Sub(left, right)
        }
      }
    def aexp  : Parser[ArithExp] = term

    /* Parsing for Comparison. */
    def comp  : Parser[Comparison] =
      aexp ~ ("=" | "<=" | ">=" | "<" | ">" | "!=") ~ aexp ^^ {
        case left ~ op ~ right => (left, op, right)
      }

    /* Parsing for BoolExp. */
    def batom : Parser[BoolExp] =
      "(" ~> bexp <~ ")" | comp ^^ { BCmp(_) } | "!" ~> batom ^^ { BNot(_) }
    def bconj : Parser[BoolExp] =
      batom ~ rep("&&" ~> batom) ^^ {
        case left ~ list => (left /: list) { BConj(_, _) }
      }
    def bdisj : Parser[BoolExp] =
      bconj ~ rep("||" ~> bconj) ^^ {
        case left ~ list => (left /: list) { BDisj(_, _) }
      }
    def bexp  : Parser[BoolExp] = bdisj

    /* Parsing for Assertion. */
    def aatom: Parser[Assertion] =
      "(" ~> assn <~ ")" | comp ^^ { ACmp(_) } | "!" ~> aatom ^^ { ANot(_) }
    def aconj : Parser[Assertion] =
      aatom ~ rep("&&" ~> aatom) ^^ {
        case left ~ list => (left /: list) { AConj(_, _) }
      }
    def adisj : Parser[Assertion] =
      aconj ~ rep("||" ~> aconj) ^^ {
        case left ~ list => (left /: list) { ADisj(_, _) }
      }
    def aimpl : Parser[Assertion] = 
      adisj ~ ("==>" ~> adisj) ^^ {
        case left ~ right => AImplies(left, right)
      } |
      adisj
    def assn : Parser[Assertion] = 
      aimpl |
      ("forall" ~> pvar) ~ ("," ~> aimpl) ^^ {
        case x ~ a => AForall(x, a)
      } |
      ("exists" ~> pvar) ~ ("," ~> aimpl) ^^ {
        case x ~ a => AExists(x, a)
      }

    /* Parsing for Statement and Block. */
    def block : Parser[Block] = rep(stmt)
    def stmt  : Parser[Statement] =
      pvar ~ ("[" ~> aexp <~ "]") ~ (":=" ~> aexp <~ ";") ^^ {
        case v ~ i ~ e => Write(v, i, e)
      } |
      (pvar <~ ":=") ~ (aexp <~ ";") ^^ {
        case v ~ e => Assign(v, e)
      } |
      (pvar <~ ",") ~ (pvar <~ ":=") ~ (aexp <~ ",") ~ (aexp <~ ";") ^^ {
        case v1 ~ v2 ~ e1 ~ e2 => ParAssign(v1, v2, e1, e2)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "else") ~ (block <~ "end") ^^ {
        case c ~ t ~ e => If(c, t, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "end") ^^ {
        case c ~ t => If(c, t, Nil)
      } |
      ("while" ~> (bexp ~ rep("inv" ~> assn)) <~ "do") ~ (block <~ "end") ^^ {
        case c ~ list ~ b => While(c, list, b)
      }

    /* Parsing for Program. */
    def prog   : Parser[Program] =
      ("program" ~> (pvar ~ rep("pre" ~> assn) ~ rep("post" ~> assn)) <~ "is") ~ (block <~ "end") ^^ {
        case n ~ pre ~ post ~ b => (n, pre, post, b)
      }
  }

  def replace(e: ArithExp, x: String, tmp: String): ArithExp = {
    // return e with all instances of x replaced with tmp
    return e
  }

  /* Translate an Assign statement into guarded commands. */
  def GCAssign(statement: Statement): GuardedCommand = {
    // GC(x := e) = assume tmp = x; havoc x; assume (x = e[tmp/x]);
    var x = statement.x
    var e = statement.value
    var tmp
    return Concat(Assume(Bcmp(tmp, "=", x)), 
          Concat(Havoc(x), Assume(Bcmp(x, "=", replace(e, x, tmp)))))
  }

  /* Translate a Write statement into guarded commands. */
  def GCWrite(statement: Statement): GuardedCommand = {
    // do translation here.
  }

  /* Translate a ParAssign statement into guarded commands. */
  def GCParAssign(statement: Statement): GuardedCommand = {
    // GC(x1, x2 := e1, e2) = assume tmp1 = x1; assume tmp2 = x2; havoc x1; havoc x2;
    // assume (x1 = e1[tmp1/x1]); assume (x2 = e2[tmp2/x2]);
    var x1 = statement.x1
    var x2 = statement.x2
    var e1 = statement.value1
    var e2 = statement.value2
    var tmp1
    var tmp2
    return Concat(Assume(Bcmp(tmp1, "=", x1)), 
          Concat(Assume(Bcmp(tmp2, "=", x2)), Concat(Havoc(x1), Concat(Havoc(x2),
          Concat(Assume(Bcmp(x1, "=", replace(e1, x1, tmp1))), 
          Assume(Bcmp(x2, "=", replace(e2, x2, tmp2))))))))
  }

  /* Translate an If statement into guarded commands. */
  def GCIf(statement: Statement): GuardedCommand = {
    // GC(if b then c1 else c2) = (assume b; GC(c1)) [] (assume !b; GC(c2))
    var b = statement.cond
    var c1 = statement.th
    var c2 = statement.el
    return Rect(Concat(Assume(b), GC(c1)), Concat(Assume(BNot(b)), GC(c2)))
  }

  /* Translate a While statement into guarded commands. */
  def GCWhile(statement: Statement): GuardedCommand = {
    // GC({I} while b do c) = assert I; havoc x1; ...; havoc xn; assume I;
    // (assume b; GC(c); assert I; assume false) [] assume !b
    var I = statement.inv
    var b = statement.cond
    var c = statement.body
    var havocs = havocVars(c) // Concat(havoc(x), havoc(y))
    return Concat(Assert(I), Concat(havocs, Concat(Assume(I), 
          Rect(Concat(Assume(b), Concat(GC(c), Assert(I))), Assume(Bnot(b))))))
  }

  /* Translates each statement in the block into a loop-free guarded command. */
  def GC(block: Block): GuardedCommand = {
    GuardedCommand gc = Assume(true)
    for (statement <- block) {
      if (statement.getClass == Assign) {
        gc = Concat(gc, GCAssign(statement))
      } else if (statement.getClass == Write) {
        gc = Concat(gc, GCWrite(statement))
      } else if (statement.getClass == ParAssign) {
        gc = Concat(gc, GCParAssign(statement))
      } else if (statement.getClass == If) {
        gc = Concat(gc, GCIf(statement))
      } else if (statement.getClass == While) {
        gc = Concat(gc, GCWhile(statement))
      }
    }
    return gc
  }

  /* Returns the program in loop-free guarded commands. */
  def computeGC(program: Product4): Product2 = {
    // want to return (programName, c_H)
    GuardedCommand command = GC(program[3])
    var precond
    for (pre <- program[1]) {
      precond = Concat(precond, pre)
    } 
    command = Concat(precond, command)
    for (post <- program[2]){
      command = Concat(command, post)
    }
    return (program[0], command)
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;
    var parsedProgram = parseAll(prog, reader)
    println(parsedProgram)
    //var guardedProgram = computeGC(parsedProgram)
    //var verificationConditions = genVC(guardedProgram)
  }
}
