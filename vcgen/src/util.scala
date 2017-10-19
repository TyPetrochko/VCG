/**
 * General helper functions
 */
object Util {
  def printAstHelper(prog: VCGen.Program): Unit = {
    prog match {
      case _ => println("TOKENNN");
    }
  }
  
  def printAst(tree: VCGen.ImpParser.ParseResult[VCGen.Program]): Unit = {
    printAstHelper(tree.get)
  }
}
