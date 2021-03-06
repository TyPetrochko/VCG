import scala.util.parsing.combinator._
import java.io._
import sys.process._


object VCGen {
  /* Set false for quiet, true for verbose */
  var verbose = false
  var z3dst = "z3"

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

  /* These are ONLY for GC/WP/SMT, not AST */
  case class ArrWrite(name: String, ind: ArithExp, value: ArithExp) extends ArithExp
  case class ArrayVar(name: String) extends ArithExp


  /* Comparisons of arithmetic expressions. */
  type Comparison = Product3[ArithExp, String, ArithExp]

  /* Boolean expressions. */
  trait BoolExp

  case class BCmp(cmp: Comparison) extends BoolExp
  case class BNot(b: BoolExp) extends BoolExp
  case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BParens(b: BoolExp) extends BoolExp // Not used?


  /* Statements and blocks. */
  trait Statement
  type Block = List[Statement]

  case class Assign(x: String, value: ArithExp) extends Statement
  case class Write(x: String, ind: ArithExp, value: ArithExp) extends Statement
  case class ParAssign(x1: String, x2: String, value1: ArithExp, value2: ArithExp) extends Statement
  case class If(cond: BoolExp, th: Block, el: Block) extends Statement
  case class While(cond: BoolExp, inv: List[Assertion], body: Block) extends Statement

  trait Assertion
  case class AssnCmp(c: Comparison) extends Assertion
  case class AssnNot(a: Assertion) extends Assertion
  case class AssnDisj(left: Assertion, right: Assertion) extends Assertion // OR
  case class AssnConj(left: Assertion, right: Assertion) extends Assertion // AND
  case class AssnImpl(left: Assertion, right: Assertion) extends Assertion
  case class AssnForall(x: List[String], assn: Assertion) extends Assertion
  case class AssnExists(x: List[String], assn: Assertion) extends Assertion
  case class AssnParens(a: Assertion) extends Assertion


  /* Complete programs. */
  type Program = Product4[String, List[Assertion], List[Assertion], Block]


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
      "(" ~> bexp <~ ")" |
      comp ^^ { BCmp(_) } |
      "!" ~> batom ^^ { BNot(_) }
    def bconj : Parser[BoolExp] =
      batom ~ rep("&&" ~> batom) ^^ {
        case left ~ list => (left /: list) { BConj(_, _) }
      }
    def bdisj : Parser[BoolExp] =
      bconj ~ rep("||" ~> bconj) ^^ {
        case left ~ list => (left /: list) { BDisj(_, _) }
      }
    def bexp  : Parser[BoolExp] = bdisj

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
      ("while" ~> (bexp ~ rep("inv" ~> assnexp)) <~ "do") ~ (block <~ "end") ^^ {
        case c ~ i ~ b => While(c, i, b)
      }

    // My parsers:
    def assnatom : Parser[Assertion] = "(" ~> assnexp <~ ")" |
        comp ^^ { AssnCmp(_) } |
        "!" ~> assnatom ^^ { AssnNot(_) } |
        ("forall" ~> rep(pvar) <~ ",") ~ assnexp ^^ {
          case list ~ a => { AssnForall(list, a) }
        } |
        ("exists" ~> rep(pvar) <~ ",") ~ assnexp ^^ {
          case list ~ a => { AssnExists(list, a) }
        }
    def assnconj : Parser[Assertion] =
      assnatom ~ rep("&&" ~> assnatom) ^^ {
        case left ~ list => (left /: list) { AssnConj(_, _) }
      }
    def assndisj : Parser[Assertion] =
      assnconj ~ rep("||" ~> assnconj) ^^ {
        case left ~ list => (left /: list) { AssnDisj(_, _) }
      }
    // Beware - this might imply backwards depending on how "/:" works
    def assnimpl : Parser[Assertion] =
      assndisj ~ rep("==>" ~> assndisj) ^^ {
        case left ~ list => (left /: list) { AssnImpl(_, _) }
      }
    def assnforall : Parser[Assertion] =
      ("forall" ~> rep(pvar) <~ ",") ~ assndisj ^^ {
        case list ~ a => { AssnForall(list, a) }
      }
    def assnexists : Parser[Assertion] =
      ("exists" ~> rep(pvar) <~ ",") ~ assnforall ^^ {
        case list ~ a => { AssnExists(list, a) }
      }
    def assnexp : Parser[Assertion] = assnimpl
    
    /* Parsing for Program. */
    def prog   : Parser[Program] =
      (("program" ~> pvar) ~ rep("pre" ~> assnexp) 
          ~ (rep("post" ~> assnexp) <~ "is")) ~ (block <~ "end") ^^ {
        case n ~ pre ~ post ~ b => (n, pre, post, b)
      }
  }

  def normalizeInvariants(invs : List[Assertion]) : Assertion = {
    invs match {
      case List() => AssnCmp((Num(1), "=", Num(1))) // True
      case List(i) => i // Single invariant
      case _ => invs.reduceLeft((i1, i2) => AssnConj(i1, i2))
    }
  }

  def main(args: Array[String]): Unit = {
    if(args.contains("-v"))
      verbose = true
    
    val reader = new FileReader(args(0))
    import ImpParser._;
    val result = parseAll(prog, reader)
    val progname = result.get._1
    val precondition = normalizeInvariants(result.get._2)
    val postcondition = normalizeInvariants(result.get._3)
    val body = result.get._4
    
    val gc = body match {
      case List() => Util.mergeGC(
          GuardedCommands.GCAssume(GuardedCommands.GCInvariant(precondition)),
          GuardedCommands.GCAssertion(postcondition)
        )
      case _ => Util.mergeGC(
          GuardedCommands.GCAssume(GuardedCommands.GCInvariant(precondition)),
          GuardedCommands.guard(body),
          GuardedCommands.GCAssertion(postcondition)
        )
    }
    val wp = WeakestPrecondition.wp(gc, GuardedCommands.getTrueyAssn)
    val z3str = Smt.getSmtString(wp)


    val tmp = Seq("mktemp").!!.trim
    new PrintWriter(tmp) { write(z3str); close }
    val out = Seq(z3dst, "-smt2", tmp).!!.trim

    if(verbose) {
      println("** AST: **")
      println(Util.prettyPrint(result))
      println("** Guarded Commands **")
      println(Util.printGC(gc))
      println("")
      // Start with program precondition as WP
      println("** Weakest Precondition (with post condition: 1=1) **")
      println(Util.prettyPrint(wp))
      println("")
      println("** Z3 String **")
      // WP should imply postcondition
      println(z3str)
    }

    if(out == "sat")
      println("Invalid")
    else if(out =="unsat")
      println("Valid")
    else
      println("unknown z3 output: "+out)
  }
}
