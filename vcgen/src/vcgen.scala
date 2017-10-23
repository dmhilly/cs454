import scala.util.parsing.combinator._
import java.io.FileReader
import scala.collection.mutable.ArrayBuffer

// TODO:
// 1. parser written but faulty (find.imp not working for example)
// 2. Add the extra things from Bill’s list
// 3. what to name temporary variables

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
  case class BAssume(a: BoolExp) extends GuardedCommand
  case class Assert(a: Assertion) extends GuardedCommand
  case class Havoc(x: String) extends GuardedCommand
  case class Concat(c1: GuardedCommand, c2: GuardedCommand) extends GuardedCommand
  case class Rect(c1: GuardedCommand, c2: GuardedCommand) extends GuardedCommand

  trait WeakestPrecondition

  case class State(b: Assertion) extends WeakestPrecondition

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

  /* Concats two guarded commands together, unless one is null. */
  def smartConcat(gc1: GuardedCommand, gc2: GuardedCommand): GuardedCommand = {
    if (gc1 == null){
      return gc2
    } else if (gc2 == null){
      return gc1
    }
    return Concat(gc1, gc2)
  }

  /* Constructs a guarded command which performs the havoc function on all vars in the block. */
  def havocVars(b: Block): GuardedCommand = {
    var gc : GuardedCommand = null 
    for (statement <- b) {
      if (statement.isInstanceOf[Assign]) {
        var aStatement = statement.asInstanceOf[Assign]
        gc = smartConcat(gc, Havoc(aStatement.x))
      } else if (statement.isInstanceOf[ParAssign]) {
        var pStatement = statement.asInstanceOf[ParAssign]
        gc = smartConcat(gc, Concat(Havoc(pStatement.x1), Havoc(pStatement.x2)))
      } else if (statement.isInstanceOf[Write]) {
        var wStatement = statement.asInstanceOf[Write]
        gc = smartConcat(gc, Havoc(wStatement.x))
      } else if (statement.isInstanceOf[If]) {
        var iStatement = statement.asInstanceOf[If]
        gc = smartConcat(gc, Concat(havocVars(iStatement.th), havocVars(iStatement.el)))
      } else { // while
        var wStatement = statement.asInstanceOf[While]
        gc = smartConcat(gc, havocVars(wStatement.body))
      }
    }
    return gc
  }

  /* Returns "Assert(I)", ie. the Assert function applied to every assertion in I. */
  def assertAll(I: List[Assertion]): GuardedCommand = {
    var gc : GuardedCommand = null
    for (assertion <- I){
      gc = smartConcat(gc, Assert(assertion))
    }
    return gc
  }

  /* Returns "Assume(I)", ie. the Assume function applied to every assertion in I. */
  def assumeAll(I: List[Assertion]): GuardedCommand = {
    var gc : GuardedCommand = null
    for (assertion <- I){
      gc = smartConcat(gc, Assume(assertion))
    }
    return gc
  }

  /* Returns expression e with all instances of x replaced with tmp. */
  def replace(e: ArithExp, x: String, tmp: String): ArithExp = {
    if (e.isInstanceOf[Num]){
      return e
    } else if (e.isInstanceOf[Var]){
      var ve = e.asInstanceOf[Var]
      if (ve.name == x) {
        return Var(tmp)
      } else {
        return ve
      }
    } else {
      if (e.isInstanceOf[Read]) {
        var re = e.asInstanceOf[Read]
        return Read(re.name, replace(re.ind, x, tmp))
      } else if (e.isInstanceOf[Add]) {
        var ae = e.asInstanceOf[Add]
        return Add(replace(ae.left, x, tmp), replace(ae.right, x, tmp))
      } else if (e.isInstanceOf[Sub]) {
        var se = e.asInstanceOf[Sub]
        return Sub(replace(se.left, x, tmp), replace(se.right, x, tmp))
      } else if (e.isInstanceOf[Mul]) {
        var me = e.asInstanceOf[Mul]
        return Mul(replace(me.left, x, tmp), replace(me.right, x, tmp))
      } else if (e.isInstanceOf[Div]) {
        var de = e.asInstanceOf[Div]
        return Div(replace(de.left, x, tmp), replace(de.right, x, tmp))
      } else if (e.isInstanceOf[Mod]) {
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
    var tmp = x + "tmp"
    return Concat(Assume(ACmp((Var(tmp), "=", Var(x)))), 
          Concat(Havoc(x), Assume(ACmp((Var(x), "=", replace(e, x, tmp))))))
  }

  /* Translate a Write statement into guarded commands. */
  def GCWrite(statement: Write): GuardedCommand = {
    // GC(a[i] := v) = assume tmp = a; havoc a; assume (a = write(tmp, i, v))
    var a = statement.x
    var i = statement.ind
    var v = statement.value
    var tmp = a + "tmp"
    return Concat(Assume(ACmp((Var(tmp), "=", Var(a)))), Concat(Havoc(a), 
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
    var tmp1 = x1 + "tmp"
    var tmp2 = x2 + "tmp"
    return Concat(Assume(ACmp((Var(tmp1), "=", Var(x1)))), 
          Concat(Assume(ACmp((Var(tmp2), "=", Var(x2)))), Concat(Havoc(x1), Concat(Havoc(x2),
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
    return smartConcat(assertions, smartConcat(havocs, smartConcat(assumptions, 
          Rect(Concat(BAssume(b), Concat(GC(c), 
          assertions)), BAssume(BNot(b))))))
  }

  /* Translates each statement in the block into a loop-free guarded command. */
  def GC(block: Block): GuardedCommand = {
    var gc : GuardedCommand = null
    for (statement <- block) {
      if (statement.isInstanceOf[Assign]) {
        gc = smartConcat(gc, GCAssign(statement.asInstanceOf[Assign]))
      } else if (statement.isInstanceOf[Write]) {
        gc = smartConcat(gc, GCWrite(statement.asInstanceOf[Write]))
      } else if (statement.isInstanceOf[ParAssign]) {
        gc = smartConcat(gc, GCParAssign(statement.asInstanceOf[ParAssign]))
      } else if (statement.isInstanceOf[If]) {
        gc = smartConcat(gc, GCIf(statement.asInstanceOf[If]))
      } else if (statement.isInstanceOf[While]) {
        gc = smartConcat(gc, GCWhile(statement.asInstanceOf[While]))
      }
    }
    return gc
  }

  /* Returns the program in loop-free guarded commands. */
  def computeGC(pre: Preconditions, post: Postconditions, block: Block): GuardedCommand = {
    // want to return (programName, c_H)
    var command : GuardedCommand = GC(block)
    command = smartConcat(assumeAll(pre), smartConcat(command, assumeAll(post)))
    return command
  }

  def replaceAssertion(assert: Assertion, x: String, tmp: String): Assertion = {
    if (assert.isInstanceOf[ACmp]) {
      var cassert = assert.asInstanceOf[ACmp]
      return ACmp(replace(cassert.cmp._1, x, tmp), cassert.cmp._2, 
        replace(cassert.cmp._3, x, tmp))
    } else if (assert.isInstanceOf[ANot]) {
      var nassert = assert.asInstanceOf[ANot]
      return ANot(replaceAssertion(nassert.a, x, tmp))
    } else if (assert.isInstanceOf[ADisj]) {
      var dassert = assert.asInstanceOf[ADisj]
      return ADisj(replaceAssertion(dassert.left, x, tmp), 
        replaceAssertion(dassert.right, x, tmp))
    } else if (assert.isInstanceOf[AConj]) {
      var coassert = assert.asInstanceOf[AConj]
      return AConj(replaceAssertion(coassert.left, x, tmp),
        replaceAssertion(coassert.right, x, tmp))
    } else if (assert.isInstanceOf[AImplies]) {
      var iassert = assert.asInstanceOf[AImplies]
      return AImplies(replaceAssertion(iassert.left, x, tmp),
        replaceAssertion(iassert.right, x, tmp))
    } else if (assert.isInstanceOf[AForall]) {
      var fassert = assert.asInstanceOf[AForall]
      return AForall(fassert.x, replaceAssertion(fassert.a, x, tmp))
    } else if (assert.isInstanceOf[AExists]) {
      var eassert = assert.asInstanceOf[AExists]
      return AExists(eassert.x, replaceAssertion(eassert.a, x, tmp))
    } else if (assert.isInstanceOf[AParens]) {
      var passert = assert.asInstanceOf[AParens]
      return AParens(replaceAssertion(passert.a, x, tmp))
    } else {
      return null
    }
  }

  def boolToAssn(be: BoolExp): Assertion = {
    if (be.isInstanceOf[BCmp]) {
      var bc = be.asInstanceOf[BCmp]
      return ACmp(bc.cmp._1, bc.cmp._2, bc.cmp._3)
    } else if (be.isInstanceOf[BNot]) {
      var bn = be.asInstanceOf[BNot]
      return ANot(boolToAssn(bn.b))
    } else if (be.isInstanceOf[BDisj]) {
      var bd = be.asInstanceOf[BDisj]
      return ADisj(boolToAssn(bd.left), boolToAssn(bd.right))
    } else if (be.isInstanceOf[BConj]) {
      var bco = be.asInstanceOf[BConj]
      return AConj(boolToAssn(bco.left), boolToAssn(bco.right))
    } else {
      var bp = be.asInstanceOf[BParens]
      return AParens(boolToAssn(bp.b))
    }
  }

  /* Translates the guarded program into a verification condition */
  def genVC(gC: GuardedCommand, b: Assertion): Assertion = {
    var wp : Assertion = null
    if (gC.isInstanceOf[Assume]) {
      var assume = gC.asInstanceOf[Assume]
      return AImplies(assume.a, b)
    } else if (gC.isInstanceOf[BAssume]) {
      var bassume = gC.asInstanceOf[BAssume]
      var assnexp = boolToAssn(bassume.a)
      return AImplies(assnexp, b)
    } else if (gC.isInstanceOf[Assert]) {
      var assert = gC.asInstanceOf[Assert]
      return AConj(assert.a, b)
    } else if (gC.isInstanceOf[Havoc]) {
      var havoc = gC.asInstanceOf[Havoc]
      return replaceAssertion(b, havoc.x, havoc.x + "frsh") //tmp == null???
    } else if (gC.isInstanceOf[Concat]) {
      var concat = gC.asInstanceOf[Concat]
      return genVC(concat.c1, genVC(concat.c2, b))
    } else if (gC.isInstanceOf[Rect]){
      var rect = gC.asInstanceOf[Rect]
      return AConj(genVC(rect.c1, b), genVC(rect.c2, b))
    } else { // gC is null
      return null
    }
  }

  /* Declare all vars seen in the program. */
  def declareVars(vars: Array[String]): String = {
    var declaration : String = ""
    for (v <- vars){
       declaration += "(declare-fun " + v + "() Int)\n" // always int?? idk.
    }
    return declaration
  }

  def SMTAhelper(vc: ArithExp, vars: ArrayBuffer[String]): (String, ArrayBuffer[String]) = {
    if (vc.isInstanceOf[Num]){
      var num = vc.asInstanceOf[Num]
      return (num.value.toString, vars)
    } else if (vc.isInstanceOf[Var]) {
      var v = vc.asInstanceOf[Var]
      if (vars.find(_ == v.name) == None){
        vars += v.name
      }
      return (v.name, vars)
    // } else if (vc.isInstanceOf[Read]) {
    //   var re = vc.asInstanceOf[Read]
    //   return "\n(+" + SMTAhelper(ae.left, vars) + SMTAhelper(ae.right, vars) + ")"
    } else if (vc.isInstanceOf[Add]) {
      var ae = vc.asInstanceOf[Add]
      var val1 = SMTAhelper(ae.left, vars)
      var val2 = SMTAhelper(ae.right, val1._2)
      return ("(+ " + val1._1 + " " + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[Sub]) {
      var se = vc.asInstanceOf[Sub]
      var val1 = SMTAhelper(se.left, vars)
      var val2 = SMTAhelper(se.right, val1._2)
      return ("(- " + val1._1 + " " + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[Mul]) {
      var me = vc.asInstanceOf[Mul]
      var val1 = SMTAhelper(me.left, vars)
      var val2 = SMTAhelper(me.right, val1._2)
      return ("(* " + val1._1 + " " + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[Div]) {
      var de = vc.asInstanceOf[Div]
      var val1 = SMTAhelper(de.left, vars)
      var val2 = SMTAhelper(de.right, val1._2)
      return ("(div " + val1._1 + " " + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[Mod]) {
      var me = vc.asInstanceOf[Mod]
      var val1 = SMTAhelper(me.left, vars)
      var val2 = SMTAhelper(me.right, val1._2)
      return ("(mod " + val1._1 + " " + val2._1 +")", val2._2)
    } else { // Parens
      var pe = vc.asInstanceOf[Parens]
      return SMTAhelper(pe.a, vars)
    }
  }

  /* Translates a single statement into SMT. */
  def SMThelper(vc: Assertion, vars: ArrayBuffer[String]): (String, ArrayBuffer[String]) = {
    // Q: 1) do we have to support functions
    if (vc.isInstanceOf[ACmp]) {
      var ac = vc.asInstanceOf[ACmp]
      var val1 = SMTAhelper(ac.cmp._1, vars)
      var val2 = SMTAhelper(ac.cmp._3, val1._2) 
      return ("(" + ac.cmp._2 + " " + val1._1 + " " + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[ANot]){
      var an = vc.asInstanceOf[ANot]
      var val1 = SMThelper(an.a, vars) 
      return ("(not" + val1._1 + ")", vars)
    } else if (vc.isInstanceOf[ADisj]){
      var ad = vc.asInstanceOf[ADisj]
      var val1 = SMThelper(ad.left, vars) 
      var val2 = SMThelper(ad.right, val1._2)
      return ("(or " + val1._1 + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[AConj]){
      var aco = vc.asInstanceOf[AConj]
      var val1 = SMThelper(aco.left, vars) 
      var val2 = SMThelper(aco.right, val1._2)
      return ("(and " + val1._1  + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[AImplies]){
      var ai = vc.asInstanceOf[AImplies]
      var val1 = SMThelper(ai.left, vars)
      var val2 = SMThelper(ai.right, val1._2)
      return ("(=> " + val1._1 + val2._1 + ")", val2._2)
    } else if (vc.isInstanceOf[AForall]){
      var af = vc.asInstanceOf[AForall]
      var val1 = SMThelper(af.a, vars)
      return ("(forall (" + af.x + " Int)" + val1._1 + ")", val1._2)
    } else if (vc.isInstanceOf[AExists]){
      var ae = vc.asInstanceOf[AExists]
      var val1 = SMThelper(ae.a, vars)
      return ("(exists (" + ae.x + " Int)" + val1._1 + ")", val1._2)
    } else if (vc.isInstanceOf[AParens]){
      var ap = vc.asInstanceOf[AParens]
      return SMThelper(ap.a, vars)
    } else {
      return null
    }
  }
  /* Translates verification conditions into the SMT Lib format. */
  def vcToSMT(vc: Assertion): String = {
    var SMTprogram : String = "(set-option :produce-models true)\n(set-logic QF_LIA)\n"
    var variables : ArrayBuffer[String] = ArrayBuffer[String]()// array of seen variables
    var body = SMThelper(vc, variables)
    var val1 = body._1
    var val2 = body._2
    if (val1 == null) {
      val1 = "true";
    }
    return SMTprogram + declareVars(val2.toArray) + 
    "(assert " + val1 + ")" + "\n(check-sat)\n(get-model)"
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;
    var parsedProgram = parseAll(prog, reader)
    // println(parsedProgram)
    val preconditions = parsedProgram.get._2
    val postconditions = parsedProgram.get._3
    val block = parsedProgram.get._4
    var guardedProgram = computeGC(preconditions, postconditions, block)
    // println(guardedProgram)
    // What to do to start with TRUE ????????
    var verificationConditions = genVC(guardedProgram, ACmp((Num(1), "=", Num(1))))
    // println(verificationConditions)
    var smtLibFormat = vcToSMT(verificationConditions)
    println(smtLibFormat)
  }
}