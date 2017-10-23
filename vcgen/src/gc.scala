/* Author: Tyler Petrochko */

/**
 * Convert AST to Loop-Free Guarded Commands. See Lec #5/#8 for these rules
 */
object GuardedCommands {
  
  trait GCAssumption
  case class GCBoolExp(b: VCGen.BoolExp) extends GCAssumption
  case class GCCheckWrite(x: String, arr: String, ind: VCGen.ArithExp,
    v: VCGen.ArithExp) extends GCAssumption
  case class GCInvariant(i: VCGen.Assertion) extends GCAssumption

  trait GC
  case class GCAssume(a : GCAssumption) extends GC
  case class GCHavoc(x: String) extends GC
  case class GCSeq(c1:GC, c2:GC) extends GC
  case class GCBranch(c1:GC, c2:GC) extends GC // Rectangle thingy
  case class GCAssertion(a: VCGen.Assertion) extends GC

  // Get a fresh var; naming convention: "#1", "#2", "#3", etc.
  private var count = 0
  def getFreshVar : String = {
    count = count + 1
    "#"+count
  }

  def gcAssumeEquals(x: String, e: VCGen.ArithExp) : GCAssume = {
    GCAssume(GCBoolExp(VCGen.BCmp(VCGen.Var(x), "=", e)))
  }

  def getVarsInStm(stm: VCGen.Statement) : Set[String] = {
    stm match {
      case VCGen.Assign(x, v) => Set(x)
      case VCGen.Write(x, i, v) => Set(x)
      case VCGen.ParAssign(x1, x2, v1, v2) => Set(x1, x2)
      case VCGen.If(cond, th, el) => getVarsInBlock(th)++getVarsInBlock(el)
      case VCGen.While(cond, inv, body) => getVarsInBlock(body)
    }
  }

  def getVarsInBlock(block: VCGen.Block) : Set[String] = {
    var found = new scala.collection.mutable.HashSet[String]()
    
    for(stm <- block; x <- getVarsInStm(stm)){
      found += x
    }
    found.toSet
  }

  // We have no inherent "False" in our BoolExp
  def getFalsey : VCGen.BoolExp = {
    VCGen.BCmp((VCGen.Num(0), "=", VCGen.Num(1)))
  }

  def getTrueyAssn : VCGen.Assertion = {
    VCGen.AssnCmp((VCGen.Num(1), "=", VCGen.Num(1)))
  }
  
  def mergeInvariants(invs: List[VCGen.Assertion]) : VCGen.Assertion = {
    invs.reduceLeft((i1, i2) => VCGen.AssnConj(i1, i2))
  }

  // e[r/x]
  def replace(e: VCGen.ArithExp, r: String, x: String) : VCGen.ArithExp = {
    e match {
      case VCGen.Num(v) => VCGen.Num(v)
      case VCGen.Var(s) => VCGen.Var(if (s == x) r else s)
      case VCGen.Read(s, ind) => 
        VCGen.Read(if (s == x) r else s, replace(ind, r, x))
      case VCGen.Add(le, ri) => VCGen.Add(replace(le, r, x), replace(ri, r, x))
      case VCGen.Sub(le, ri) => VCGen.Sub(replace(le, r, x), replace(ri, r, x))
      case VCGen.Mul(le, ri) => VCGen.Mul(replace(le, r, x), replace(ri, r, x))
      case VCGen.Div(le, ri) => VCGen.Div(replace(le, r, x), replace(ri, r, x))
      case VCGen.Mod(le, ri) => VCGen.Mod(replace(le, r, x), replace(ri, r, x))
      case VCGen.Parens(a) => VCGen.Parens(replace(a, r, x))
    }
  }

  // Tree-ify multiple GC
  def join(gcs: GC*) : GC = {
    gcs.reduceLeft((l, r) => GCSeq(l,r))
  }

  def guard(b: VCGen.Block) : GC = {
    join(b.map((s) => guard(s)): _*) // Scala's _* "Splat" operator - cool!
  }

  def guard(s: VCGen.Statement) : GC = {
    s match {
      case VCGen.Assign(x, e) => {
        val tmp = getFreshVar
        join(
            gcAssumeEquals(tmp, VCGen.Var(x)),
            GCHavoc(x),
            gcAssumeEquals(x, replace(e, tmp, x))
          )
      }
      case VCGen.Write(x, ind, v) => {
        val tmp = getFreshVar
        join(
            gcAssumeEquals(tmp, VCGen.Var(x)),
            GCHavoc(x),
            GCAssume(GCCheckWrite(x, tmp, replace(ind, tmp, x), replace(v, tmp, x)))
          )
      }
      case VCGen.ParAssign(x1, x2, v1, v2) => {
        val tmp = getFreshVar
        join(
            guard(VCGen.Assign(tmp, v2)),
            guard(VCGen.Assign(x1, v1)),
            guard(VCGen.Assign(x2, VCGen.Var(tmp)))
          )
      }
      case VCGen.If(cond, th, el) => {
        GCBranch(
            join(GCAssume(GCBoolExp(cond)), guard(th)),
            join(GCAssume(GCBoolExp(VCGen.BNot(cond))), guard(el))
          )
      }
      case VCGen.While(cond, invs, body) => {
        val varsUsed = getVarsInBlock(body).toList
        val havocStms = join(varsUsed.map(s => GCHavoc(s)): _*) // Splat operator! Wooo!
        val inv = invs match {
          case List() => getTrueyAssn
          case List(i) => i
          case other => mergeInvariants(other)
        }
        join(
            GCAssertion(inv),
            havocStms, 
            GCAssume(GCInvariant(inv)),
            GCBranch(
                join(
                    GCAssume(GCBoolExp(cond)),
                    guard(body),
                    GCAssertion(inv),
                    GCAssume(GCBoolExp(getFalsey))
                  ),
                GCAssume(GCBoolExp(VCGen.BNot(cond)))
              )
          )
      }
      case _ => null
    }
  }
}
