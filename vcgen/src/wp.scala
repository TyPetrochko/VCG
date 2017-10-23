/* Author: Tyler Petrochko */

/**
 * Calculate weakest precondition from guarded commands
 */
object WeakestPrecondition {

  // Get a fresh var; naming convention: "$1", "$2", "$3", etc.
  private var count = 0
  def getFreshVar : String = {
    count = count + 1
    "$"+count
  }

  // Helper function for main replace
  def replace(s: String, r: String, x: String) : String = {
    if(s == x) r else s
  }

  // Another helper just for VCGen.asswertion
  def replace(a: VCGen.Assertion, r: String, x: String) : VCGen.Assertion = {
    a match {
      case VCGen.AssnCmp((e1, s, e2)) => VCGen.AssnCmp((
        GuardedCommands.replace(e1, r, x), replace(s, r, x), GuardedCommands.replace(e2, r, x)))
      case VCGen.AssnNot(a2: VCGen.Assertion) => VCGen.AssnNot(replace(a2, r, x))
      case VCGen.AssnDisj(le, ri) => VCGen.AssnDisj(replace(le, r, x), replace(ri, r, x))
      case VCGen.AssnConj(le, ri) => VCGen.AssnConj(replace(le, r, x), replace(ri, r, x))
      case VCGen.AssnImpl(le, ri) => VCGen.AssnImpl(replace(le, r, x), replace(ri, r, x))
      case VCGen.AssnForall(xs, a2) => VCGen.AssnForall(
        xs.map(str => replace(str, r, x)), replace(a2, r, x))
      case VCGen.AssnExists(xs, a2) => VCGen.AssnExists(
        xs.map(str => replace(str, r, x)), replace(a2, r, x))
      case VCGen.AssnParens(a2) => VCGen.AssnParens(replace(a2, r, x))
    }
  }

  def boolExpToAssertion(b: VCGen.BoolExp) : VCGen.Assertion = {
    b match {
      case VCGen.BCmp(c) => VCGen.AssnCmp(c)
      case VCGen.BNot(cond) => VCGen.AssnNot(boolExpToAssertion(cond))
      case VCGen.BDisj(l, r) => VCGen.AssnDisj(boolExpToAssertion(l), boolExpToAssertion(r))
      case VCGen.BConj(l, r) => VCGen.AssnConj(boolExpToAssertion(l), boolExpToAssertion(r))
      case VCGen.BParens(cond) => VCGen.AssnParens(boolExpToAssertion(cond))
    }
  }

  // Main external call
  def wp(gc: GuardedCommands.GC, a: VCGen.Assertion) : VCGen.Assertion = {
    gc match {
      case GuardedCommands.GCAssume(
        GuardedCommands.GCBoolExp(b)) => VCGen.AssnImpl(boolExpToAssertion(b), a)
      case GuardedCommands.GCAssume(
        GuardedCommands.GCInvariant(i)) => VCGen.AssnImpl(i, a)
      case GuardedCommands.GCHavoc(x) => {
        val tmp = getFreshVar
        replace(a, tmp, x)
      }
      case GuardedCommands.GCSeq(c1, c2) => wp(c1, wp(c2, a))
      case GuardedCommands.GCBranch(c1, c2) => VCGen.AssnConj(
        wp(c1, a), wp(c2, a))
      case GuardedCommands.GCAssertion(assn) => VCGen.AssnConj(assn, a)
    }
  }
}
