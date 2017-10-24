/* Author: Tyler Petrochko */

/**
 * General helper functions
 */
object Util {
  
  def mergeGC(gc1: GuardedCommands.GC, gc2: GuardedCommands.GC) = {
    rewrapGc(unwrapGc(gc1)++unwrapGc(gc2))
  }

  def mergeGC(gc1: GuardedCommands.GC, gc2: GuardedCommands.GC, gc3: GuardedCommands.GC) = {
    rewrapGc(unwrapGc(gc1)++unwrapGc(gc2)++unwrapGc(gc3))
  }

  def unwrapGc(gc: GuardedCommands.GC) : List[GuardedCommands.GC] = {
    gc match {
      case GuardedCommands.GCSeq(c1, c2) => unwrapGc(c1)++unwrapGc(c2)
      case _ => List(gc)
    }
  }

  def rewrapGc(gcs : List[GuardedCommands.GC]) : GuardedCommands.GC = {
    gcs.reduceLeft((l, r) => GuardedCommands.GCSeq(l,r))
  }

  def printAstHelper(prog: VCGen.Program): String = {
    var toReturn = "Name: "+prog._1+"\n"
    toReturn += "Preconditions: "+prog._2+"\n"
    toReturn += "Postconditions: "+prog._3+"\n"
    toReturn += "Body: "+prog._4
    toReturn
  }
  
  def printAst(tree: VCGen.ImpParser.ParseResult[VCGen.Program]): Unit = {
    println(printAstHelper(tree.get))
  }

  def printGC(tree: GuardedCommands.GC) : String = {
    tree match {
      case GuardedCommands.GCAssume(GuardedCommands.GCBoolExp(b)) => "assume "+b+";"
      case GuardedCommands.GCAssume(GuardedCommands.GCInvariant(i)) => "assume "+i+";"
      case GuardedCommands.GCHavoc(x) => "havoc "+x+";"
      case GuardedCommands.GCSeq(c1, c2) => printGC(c1)+"\n"+printGC(c2)
      case GuardedCommands.GCBranch(c1, c2) => "("+printGC(c1)+")[]"+"\n"+"("+printGC(c2)+")"
      case GuardedCommands.GCAssertion(a) => "assert "+a+";"
      case null => "null"
    }
  }

  /**
   * Adapted from: https://gist.github.com/carymrobbins/7b8ed52cd6ea186dbdf8
   *
   * Pretty prints a Scala value similar to its source represention.
   * Particularly useful for case classes.
   * @param a - The value to pretty print.
   * @param indentSize - Number of spaces for each indent.
   * @param maxElementWidth - Largest element size before wrapping.
   * @param depth - Initial depth to pretty print indents.
   * @return
   */
  def prettyPrint(
      a: Any, indentSize: Int = 2, maxElementWidth: Int = 30, depth: Int = 0): String = {
    val indent = " " * depth * indentSize
    val fieldIndent = indent + (" " * indentSize)
    val thisDepth = prettyPrint(_: Any, indentSize, maxElementWidth, depth)
    val nextDepth = prettyPrint(_: Any, indentSize, maxElementWidth, depth + 1)
    a match {
      case null => "null"
      // Make Strings look similar to their literal form.
      case s: String =>
        val replaceMap = Seq(
          "\n" -> "\\n",
          "\r" -> "\\r",
          "\t" -> "\\t",
          "\"" -> "\\\""
        )
        '"' + replaceMap.foldLeft(s) { case (acc, (c, r)) => acc.replace(c, r) } + '"'
      // For an empty Seq just use its normal String representation.
      case xs: Seq[_] if xs.isEmpty => xs.toString()
      case xs: Seq[_] =>
        // If the Seq is not too long, pretty print on one line.
        val resultOneLine = xs.map(nextDepth).toString()
        if (resultOneLine.length <= maxElementWidth) return resultOneLine
        // Otherwise, build it with newlines and proper field indents.
        val result = xs.map(x => s"\n$fieldIndent${nextDepth(x)}").toString()
        result.substring(0, result.length - 1) + "\n" + indent + ")"
      // Product should cover case classes.
      case p: Product =>
        val prefix = p.productPrefix
        // We'll use reflection to get the constructor arg names and values.
        val cls = p.getClass
        val fields = cls.getDeclaredFields.filterNot(_.isSynthetic).map(_.getName)
        val values = p.productIterator.toSeq
        // If we weren't able to match up fields/values, fall back to toString.
        if (fields.length != values.length) return p.toString
        fields.zip(values).toList match {
          // If there are no fields, just use the normal String representation.
          case Nil => p.toString
          // If there is just one field, let's just print it as a wrapper.
          case (_, value) :: Nil => s"$prefix(${thisDepth(value)})"
          // If there is more than one field, build up the field names and values.
          case kvps =>
            val prettyFields = kvps.map { case (k, v) => s"$fieldIndent${nextDepth(v)}" }
            // If the result is not too long, pretty print on one line.
            val resultOneLine = s"$prefix(${prettyFields.mkString(", ")})"
            if (resultOneLine.length <= maxElementWidth) return resultOneLine
            // Otherwise, build it with newlines and proper field indents.
            s"$prefix(\n${prettyFields.mkString(",\n")}\n$indent)"
        }
      // If we haven't specialized this type, just use its toString.
      case _ => a.toString
    }
  }
}
