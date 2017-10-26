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
        print("havoc " + aStatement.x + "; ")
      } else if (statement.isInstanceOf[ParAssign]) {
        var pStatement = statement.asInstanceOf[ParAssign]
        gc = smartConcat(gc, Concat(Havoc(pStatement.x1), Havoc(pStatement.x2)))
         print("havoc " + pStatement.x1 + "; havoc" + pStatement.x2 + "; ")
      } else if (statement.isInstanceOf[Write]) {
        var wStatement = statement.asInstanceOf[Write]
        gc = smartConcat(gc, ArrayHavoc(wStatement.x))
        print("havoc " + wStatement.x + "; ")
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
      } else if (e.isInstanceOf[Parens]){ 
        var pe = e.asInstanceOf[Parens]
        return Parens(replace(pe.a, x, tmp))
      } else{ // AWrite
        var we = e.asInstanceOf[AWrite]
        return AWrite(we.a, replace(we.i, x, tmp), replace(we.v, x, tmp))
      }
    }
  }

  def updateMap(x: String, map: scala.collection.mutable.Map[String, Int]): scala.collection.mutable.Map[String, Int] = {
    if (map.contains(x)) {
      map(x) += 1
    } else {
      map += (x -> 1)
    }
    return map
  }

  /* Translate an Assign statement into guarded commands. */
  def GCAssign(statement: Assign, vars: scala.collection.mutable.Map[String, Int]): (GuardedCommand, scala.collection.mutable.Map[String, Int]) = {
    // GC(x := e) = assume tmp = x; havoc x; assume (x = e[tmp/x]);
    var x = statement.x
    var e = statement.value
    var newVars = updateMap(x, vars)
    var tmp = x + "tmp" + newVars(x)
    println("assume " + tmp + " = " + x + "; havoc " + x + "; assume (" + 
      x + " = " + e + "[" + tmp + "/" + x + "]);")
    return (Concat(Assume(ACmp((Var(tmp), "=", Var(x)))), 
          Concat(Havoc(x), Assume(ACmp((Var(x), "=", replace(e, x, tmp)))))), newVars)
  }

  /* Translate a Write statement into guarded commands. */
  def GCWrite(statement: Write, vars: scala.collection.mutable.Map[String, Int]): (GuardedCommand, scala.collection.mutable.Map[String, Int]) = {
    // GC(a[i] := v) = assume tmp = a; havoc a; assume (a = write(tmp, i, v))
    var a = statement.x
    var i = statement.ind
    var v = statement.value
    var newVars = updateMap(a, vars)
    var tmp = a + "tmp" + newVars(a)
    println("assume " + tmp + " = " + a + "; havoc " + a + "; assume (" + 
      a + " = " + "write(" + tmp + ", " + i + ", " + v + ";")
    return (Concat(Assume(ACmp((Var(tmp), "=", Var(a)))), Concat(ArrayHavoc(a), 
      Assume(ACmp((Var(a), "=", AWrite(tmp, i, v)))))), newVars)
  }

  /* Translate a ParAssign statement into guarded commands. */
  def GCParAssign(statement: ParAssign, vars: scala.collection.mutable.Map[String, Int]): (GuardedCommand, scala.collection.mutable.Map[String, Int]) = {
    // GC(x1, x2 := e1, e2) = assume tmp1 = x1; assume tmp2 = x2; havoc x1; havoc x2;
    // assume (x1 = e1[tmp1/x1]); assume (x2 = e2[tmp2/x2]);
    var x1 = statement.x1
    var x2 = statement.x2
    var e1 = statement.value1
    var e2 = statement.value2
    var newVars = updateMap(x1, vars)
    newVars = updateMap(x2, newVars)
    var tmp1 = x1 + "tmp" + newVars(x1)
    var tmp2 = x2 + "tmp" + newVars(x2)
    println("assume " + tmp1 + " = " + x1 + "; assume " + tmp2 + " = " + x2 + 
      "; havoc " + x1 + "; havoc" + x2 + "; assume (" + x1 + " = " + e1 + 
      "[" + tmp1 + "/" + x1 + "]); assume (" + x2 + " = " + e2 + "[" + tmp2 +
      "/" + x2 + "]);")
    return (smartConcat(Assume(ACmp((Var(tmp1), "=", Var(x1)))), 
          smartConcat(Assume(ACmp((Var(tmp2), "=", Var(x2)))), smartConcat(Havoc(x1), smartConcat(Havoc(x2),
          smartConcat(Assume(ACmp((Var(x1), "=", replace(e1, x1, tmp1)))), 
          Assume(ACmp((Var(x2), "=", replace(e2, x2, tmp2))))))))), newVars)
  }

  /* Translate an If statement into guarded commands. */
  def GCIf(statement: If, vars: scala.collection.mutable.Map[String, Int]): (GuardedCommand, scala.collection.mutable.Map[String, Int]) = {
    // GC(if b then c1 else c2) = (assume b; GC(c1)) [] (assume !b; GC(c2))
    var b = statement.cond
    var c1 = statement.th
    var c2 = statement.el
    println("(assume " + b + "; ")
    var c1result = GC(c1, vars)
    println(") []")
    println("(assume !" + "b;")
    var c2result = GC(c2, c1result._2)
    println(")")
    return (Rect(smartConcat(BAssume(b), c1result._1), 
      smartConcat(BAssume(BNot(b)), c2result._1)), c2result._2)
  }

  /* Translate a While statement into guarded commands. */
  def GCWhile(statement: While, vars: scala.collection.mutable.Map[String, Int]): (GuardedCommand, scala.collection.mutable.Map[String, Int]) = {
    // GC({I} while b do c) = assert I; havoc x1; ...; havoc xn; assume I;
    // (assume b; GC(c); assert I; assume false) [] assume !b
    var I = statement.inv
    var b = statement.cond
    var c = statement.body
    println("assert " + I + ";")
    var havocs = havocVars(c)
    var assertions = assertAll(I)
    var assumptions = assumeAll(I)
    println("assume " + I + ";")
    println("(assume " + b + ";")
    var result = GC(c, vars)
    println("assert " + I + "; assume false;) [] assume !" + b + ";")
    return (smartConcat(assertions, smartConcat(havocs, smartConcat(assumptions, 
          Rect(Concat(BAssume(b), smartConcat(result._1, 
          smartConcat(assertions, Assume(ACmp((Num(1), "=", Num(0))))))), BAssume(BNot(b)))))), result._2)
  }

  /* Translates each statement in the block into a loop-free guarded command. */
  def GC(block: Block, passedVars: scala.collection.mutable.Map[String, Int]): (GuardedCommand, scala.collection.mutable.Map[String, Int]) = {
    var gc : GuardedCommand = null
    var vars = scala.collection.mutable.Map[String, Int]()
    if (passedVars != null){
      vars = passedVars
    }
    for (statement <- block) {
      if (statement.isInstanceOf[Assign]) {
        var result = GCAssign(statement.asInstanceOf[Assign], vars)
        gc = smartConcat(gc, result._1)
        vars = result._2
      } else if (statement.isInstanceOf[Write]) {
        var result = GCWrite(statement.asInstanceOf[Write], vars)
        gc = smartConcat(gc, result._1)
        vars = result._2
      } else if (statement.isInstanceOf[ParAssign]) {
        var result = GCParAssign(statement.asInstanceOf[ParAssign], vars)
        gc = smartConcat(gc, result._1)
        vars = result._2
      } else if (statement.isInstanceOf[If]) {
        var result = GCIf(statement.asInstanceOf[If], vars)
        gc = smartConcat(gc, result._1)
        vars = result._2
      } else if (statement.isInstanceOf[While]) {
        var result = GCWhile(statement.asInstanceOf[While], vars)
        gc = smartConcat(gc, result._1)
        vars = result._2
      }
    }
    return (gc, vars)
  }

  /* Returns the program in loop-free guarded commands. */
  def computeGC(pre: Preconditions, post: Postconditions, block: Block): GuardedCommand = {
    // want to return (programName, c_H)
    var result = GC(block, null)
    var command = smartConcat(assumeAll(pre), smartConcat(result._1, assertAll(post)))
    return command
  }
