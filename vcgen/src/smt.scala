/* Author: Tyler Petrochko */

/**
 * Generate z3 output
 */
object Smt {
  
  def getArrays(arith : VCGen.ArithExp) : Set[String] = {
    arith match {
      case VCGen.Num(v) => Set[String]()
      case VCGen.Var(x) => Set[String]()
      case VCGen.ArrayVar(x) => Set(x)
      case VCGen.Read(a, i) => Set(a)++getArrays(i)
      case VCGen.Add(l, r) => getArrays(l)++getArrays(r)
      case VCGen.Sub(l, r) => getArrays(l)++getArrays(r)
      case VCGen.Mul(l, r) => getArrays(l)++getArrays(r)
      case VCGen.Div(l, r) => getArrays(l)++getArrays(r)
      case VCGen.Mod(l, r) => getArrays(l)++getArrays(r)
      case VCGen.Parens(a) => getArrays(a)
      case VCGen.ArrWrite(name, i, v) => Set(name)++getArrays(i)++getArrays(v)
    }
  }
  
  def getArrays(assn : VCGen.Assertion) : Set[String] = {
    assn match {
      case VCGen.AssnCmp((a1, str, a2)) => getArrays(a1)++getArrays(a2)
      case VCGen.AssnNot(a) => getArrays(a)
      case VCGen.AssnDisj(l, r) => getArrays(l)++getArrays(r)
      case VCGen.AssnConj(l, r) => getArrays(l)++getArrays(r)
      case VCGen.AssnImpl(l, r) => getArrays(l)++getArrays(r)
      // Slight chance we need to investigate x as well...
      case VCGen.AssnForall(x, a) => getArrays(a)
      case VCGen.AssnExists(x, a) => getArrays(a)
      case VCGen.AssnParens(a) => getArrays(a)
    }
  }

  // Only non-array variables
  def getVars(arith : VCGen.ArithExp) : Set[String] = {
    arith match {
      case VCGen.Num(v) => Set[String]()
      case VCGen.Var(x) => Set(x)
      case VCGen.ArrayVar(x) => Set[String]()
      case VCGen.Read(a, i) => getVars(i)
      case VCGen.Add(l, r) => getVars(l)++getVars(r)
      case VCGen.Sub(l, r) => getVars(l)++getVars(r)
      case VCGen.Mul(l, r) => getVars(l)++getVars(r)
      case VCGen.Div(l, r) => getVars(l)++getVars(r)
      case VCGen.Mod(l, r) => getVars(l)++getVars(r)
      case VCGen.Parens(a) => getVars(a)
      case VCGen.ArrWrite(name, i, v) => getVars(i)++getVars(v)
    }
  }
  
  def getVars(assn : VCGen.Assertion) : Set[String] = {
    assn match {
      case VCGen.AssnCmp((a1, str, a2)) => getVars(a1)++getVars(a2)
      case VCGen.AssnNot(a) => getVars(a)
      case VCGen.AssnDisj(l, r) => getVars(l)++getVars(r)
      case VCGen.AssnConj(l, r) => getVars(l)++getVars(r)
      case VCGen.AssnImpl(l, r) => getVars(l)++getVars(r)
      case VCGen.AssnForall(x, a) => getVars(a)--x.toSet
      case VCGen.AssnExists(x, a) => getVars(a)--x.toSet
      case VCGen.AssnParens(a) => getVars(a)
    }
  }

  def dequantify(assn : VCGen.Assertion) : VCGen.Assertion = {
    assn match {
      case VCGen.AssnCmp(c) => VCGen.AssnCmp(c)
      case VCGen.AssnNot(a) => VCGen.AssnNot(dequantify(a))
      case VCGen.AssnDisj(l, r) => VCGen.AssnDisj(dequantify(l), dequantify(r))
      case VCGen.AssnConj(l, r) => VCGen.AssnConj(dequantify(l), dequantify(r))
      case VCGen.AssnImpl(l, r) => VCGen.AssnImpl(dequantify(l), dequantify(r))
      case VCGen.AssnForall(x, a) => dequantify(a)
      case VCGen.AssnExists(x, a) => VCGen.AssnNot(dequantify(a))
      case VCGen.AssnParens(a) => VCGen.AssnParens(dequantify(a))
    }
  }
  
  def buildSmtClause(arith: VCGen.ArithExp) : String = {
    arith match {
      case VCGen.Num(v) => ""+v
      case VCGen.Var(x) => x
      case VCGen.ArrayVar(a) => a
      case VCGen.Read(a, i) => {
        val index = buildSmtClause(i)
        s"(select $a $index)"
      }
      case VCGen.Add(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(+ $lhs $rhs)"
      }
      case VCGen.Sub(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(- $lhs $rhs)"
      }
      case VCGen.Mul(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(* $lhs $rhs)"
      }
      case VCGen.Div(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(/ $lhs $rhs)"
      }
      case VCGen.Mod(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(mod $lhs $rhs)"
      }
      case VCGen.ArrWrite(a, i, v) => {
        val index = buildSmtClause(i)
        val value = buildSmtClause(v)
        s"(store $a $index $value)"
      }
      case VCGen.Parens(a) => buildSmtClause(a)
    }
  }

  def buildSmtClause(assn: VCGen.Assertion) : String = {
    assn match {
      case VCGen.AssnCmp((a1, str, a2)) => {
        val lhs = buildSmtClause(a1)
        val rhs = buildSmtClause(a2)
        s"($str $lhs $rhs)"
      }
      case VCGen.AssnNot(a) => {
        val inner = buildSmtClause(a)
        s"(not $inner)"
      }
      case VCGen.AssnDisj(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(or $lhs $rhs)"
      }
      case VCGen.AssnConj(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(and $lhs $rhs)"
      }
      case VCGen.AssnImpl(l, r) => {
        val lhs = buildSmtClause(l)
        val rhs = buildSmtClause(r)
        s"(implies $lhs $rhs)"
      }
      case VCGen.AssnParens(a) => buildSmtClause(a)
      case VCGen.AssnForall(x, assn) => {
        val body = buildSmtClause(assn)
        val decs = x.foldLeft(" ")((total, declvar) => total+s"($declvar Int) ")
        s"(forall ($decs) $body)"
      }
      case VCGen.AssnExists(x, assn) => {
        val body = buildSmtClause(assn)
        val decs = x.foldLeft(" ")((total, declvar) => total+s"($declvar Int) ")
        s"(exists ($decs) $body)"
      }
    }
  }

  def getSmtString(assn: VCGen.Assertion) : String = {
    /**
     * TODO:
     * (x) For each var x, make a "(declare-const x Int)"
     * (x) For each array arr, make a "(declare-const arr (Array Int Int))"
     * (x) Dequantify it
     * (x) Add a "AssnNot" in front of everything -> i.e. we're checking the
     *     negation is unsatisfiable
     * (x) Recursively convert everything to list-style z3 string
     * (x) Add an (assert z3str)
     */
    val varsUsed = getVars(assn)
    val arrsUsed = getArrays(assn)

    var str = ""
    str += varsUsed.toList.foldLeft("")((str, x) => s"$str(declare-const $x Int)\n")
    str += arrsUsed.toList.foldLeft("")((str, a) => s"$str(declare-const $a (Array Int Int))\n")

    val smtClause = buildSmtClause(VCGen.AssnNot(assn))

    str += s"(assert $smtClause)\n"
    str += s"(check-sat)"
    str
  }
}
