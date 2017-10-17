import scala.util.parsing.combinator._
import java.io.FileReader

// TODO:
// 1. parser written but faulty (find.imp not working for example)
// 2. figure out all this type stuff D:
// 3. translate guarded commands into verification condition

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
  case class AWrite(a: String, i: ArithExp, v: ArithExp) extends ArithExp


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
  case class BAssume(b: BoolExp) extends GuardedCommand
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

  /* Constructs a guarded command which performs the havoc function on all vars in the block. */
  def havocVars(b: Block): GuardedCommand = {
    var gc : GuardedCommand = Assume(ACmp((Num(1), "=", Num(1)))) // assume true
    for (statement <- b) {
      if (statement.getClass == Assign) {
        var aStatement = statement.asInstanceOf[Assign]
        gc = Concat(gc, Havoc(aStatement.x))
      } else if (statement.getClass == ParAssign) {
        var pStatement = statement.asInstanceOf[ParAssign]
        gc = Concat(gc, Concat(Havoc(pStatement.x1), Havoc(pStatement.x2)))
      } else if (statement.getClass == Write) {
        var wStatement = statement.asInstanceOf[Write]
        gc = Concat(gc, Havoc(wStatement.x))
      } else if (statement.getClass == If) {
        var iStatement = statement.asInstanceOf[If]
        gc = Concat(gc, Concat(havocVars(iStatement.th), havocVars(iStatement.el)))
      } else { // while
        var wStatement = statement.asInstanceOf[While]
        gc = Concat(gc, havocVars(wStatement.body))
      }
    }
    return gc
  }

  /* Returns "Assert(I)", ie. the Assert function applied to every assertion in I. */
  def assertAll(I: List[Assertion]): GuardedCommand = {
    var gc : GuardedCommand = Assume(ACmp((Num(1), "=", Num(1)))) // assume true
    for (assertion <- I){
      gc = Concat(gc, Assert(assertion))
    }
    return gc
  }

  /* Returns "Assume(I)", ie. the Assume function applied to every assertion in I. */
  def assumeAll(I: List[Assertion]): GuardedCommand = {
    var gc : GuardedCommand = Assume(ACmp((Num(1), "=", Num(1)))) // assume true
    for (assertion <- I){
      gc = Concat(gc, Assume(assertion))
    }
    return gc
  }

  /* Returns expression e with all instances of x replaced with tmp. */
  def replace(e: ArithExp, x: String, tmp: String): ArithExp = {
    if (e.getClass == Num){
      return e
    } else if (e.getClass == Var){
      var ve = e.asInstanceOf[Var]
      if (ve.name == x) {
        return Var(tmp)
      } else {
        return ve
      }
    } else {
      if (e.getClass == Read) {
        var re = e.asInstanceOf[Read]
        return Read(re.name, replace(re.ind, x, tmp))
      } else if (e.getClass == Add) {
        var ae = e.asInstanceOf[Add]
        return Add(replace(ae.left, x, tmp), replace(ae.right, x, tmp))
      } else if (e.getClass == Sub) {
        var se = e.asInstanceOf[Sub]
        return Sub(replace(se.left, x, tmp), replace(se.right, x, tmp))
      } else if (e.getClass == Mul) {
        var me = e.asInstanceOf[Mul]
        return Mul(replace(me.left, x, tmp), replace(me.right, x, tmp))
      } else if (e.getClass == Div) {
        var de = e.asInstanceOf[Div]
        return Div(replace(de.left, x, tmp), replace(de.right, x, tmp))
      } else if (e.getClass == Mod) {
        var me = e.asInstanceOf[Mod]
        return Mod(replace(me.left, x, tmp), replace(me.right, x, tmp))
      } else { // Parens
        var pe = e.asInstanceOf[Parens]
        return Parens(replace(pe.a, x, tmp))
      }
    }
  }

  /* Translate an Assign statement into guarded commands. */
  def GCAssign(statement: Assign): GuardedCommand = {
    // GC(x := e) = assume tmp = x; havoc x; assume (x = e[tmp/x]);
    var x = statement.x
    var e = statement.value
    var tmp = null
    return Concat(Assume(ACmp((tmp, "=", Var(x)))), 
          Concat(Havoc(x), Assume(ACmp((Var(x), "=", replace(e, x, tmp))))))
  }

  /* Translate a Write statement into guarded commands. */
  def GCWrite(statement: Write): GuardedCommand = {
    // GC(a[i] := v) = assume tmp = a; havoc a; assume (a = write(tmp, i, v))
    var a = statement.x
    var i = statement.ind
    var v = statement.value
    var tmp = null
    return Concat(Assume(ACmp((tmp, "=", Var(a)))), Concat(Havoc(a), 
      Assume(ACmp((Var(a), "=", AWrite(tmp, i, v))))))
  }

  /* Translate a ParAssign statement into guarded commands. */
  def GCParAssign(statement: ParAssign): GuardedCommand = {
    // GC(x1, x2 := e1, e2) = assume tmp1 = x1; assume tmp2 = x2; havoc x1; havoc x2;
    // assume (x1 = e1[tmp1/x1]); assume (x2 = e2[tmp2/x2]);
    var x1 = statement.x1
    var x2 = statement.x2
    var e1 = statement.value1
    var e2 = statement.value2
    var tmp1 = null
    var tmp2 = null
    return Concat(Assume(ACmp((tmp1, "=", Var(x1)))), 
          Concat(Assume(ACmp((tmp2, "=", Var(x2)))), Concat(Havoc(x1), Concat(Havoc(x2),
          Concat(Assume(ACmp((Var(x1), "=", replace(e1, x1, tmp1)))), 
          Assume(ACmp((Var(x2), "=", replace(e2, x2, tmp2)))))))))
  }

  /* Translate an If statement into guarded commands. */
  def GCIf(statement: If): GuardedCommand = {
    // GC(if b then c1 else c2) = (assume b; GC(c1)) [] (assume !b; GC(c2))
    var b = statement.cond
    var c1 = statement.th
    var c2 = statement.el
    return Rect(Concat(BAssume(b), GC(c1)), 
      Concat(BAssume(BNot(b)), GC(c2)))
  }

  /* Translate a While statement into guarded commands. */
  def GCWhile(statement: While): GuardedCommand = {
    // GC({I} while b do c) = assert I; havoc x1; ...; havoc xn; assume I;
    // (assume b; GC(c); assert I; assume false) [] assume !b
    var I = statement.inv
    var b = statement.cond
    var c = statement.body
    var havocs = havocVars(c)
    var assertions = assertAll(I)
    var assumptions = assumeAll(I)
    return Concat(assertions, Concat(havocs, Concat(assumptions, 
          Rect(Concat(BAssume(b), Concat(GC(c), 
          assertions)), BAssume(BNot(b))))))
  }

  /* Translates each statement in the block into a loop-free guarded command. */
  def GC(block: Block): GuardedCommand = {
    var gc : GuardedCommand = Assume(ACmp((Num(1), "=", Num(1)))) // assume true
    for (statement <- block) {
      if (statement.getClass == Assign) {
        gc = Concat(gc, GCAssign(statement.asInstanceOf[Assign]))
      } else if (statement.getClass == Write) {
        gc = Concat(gc, GCWrite(statement.asInstanceOf[Write]))
      } else if (statement.getClass == ParAssign) {
        gc = Concat(gc, GCParAssign(statement.asInstanceOf[ParAssign]))
      } else if (statement.getClass == If) {
        gc = Concat(gc, GCIf(statement.asInstanceOf[If]))
      } else if (statement.getClass == While) {
        gc = Concat(gc, GCWhile(statement.asInstanceOf[While]))
      }
    }
    return gc
  }

  /* Returns the program in loop-free guarded commands. */
  def computeGC(pre: Preconditions, post: Postconditions, block: Block): GuardedCommand = {
    // want to return (programName, c_H)
    var command : GuardedCommand = GC(block)
    Concat(assumeAll(pre), Concat(command, assumeAll(post)))
    return command
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;
    var parsedProgram = parseAll(prog, reader)
    println(parsedProgram)
    val preconditions = parsedProgram._1
    val postconditions = parsedProgram._2
    val block = parsedProgram._3
    var guardedProgram = computeGC(preconditions, postconditions, block)
    //var verificationConditions = genVC(guardedProgram)
  }
}
