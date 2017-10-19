/**
 * General helper functions
 */
object Util {
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
}
