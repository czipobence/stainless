/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait Tactic {
  val program: Program
  val description: String

  import program.trees._
  import program.symbols._

  protected type VC = verification.VC[program.trees.type]
  protected def VC(cond: program.trees.Expr, id: Identifier, kind: VCKind, nonRemovable: Set[String] = Set()): VC = {
    // println("create VC with nonRemovable: " + nonRemovable)
    verification.VC(cond, id, kind, nonRemovable)
  }

  protected def collectForConditions[T](pf: PartialFunction[(Expr, Path),T])(e: Expr): Seq[T] = {
    new transformers.CollectorWithPC {
      val trees: program.trees.type = program.trees
      val symbols: program.symbols.type = program.symbols
      type Result = T

      private val lifted = pf.lift

      protected def step(e: Expr, env: Env): List[Result] = lifted(e, env).toList

      override protected def rec(e: Expr, env: Env): Expr = e match {
        case Annotated(_, flags) if flags contains Unchecked => e
        case _ => super.rec(e, env)
      }
    }.collect(e)
  }

  def generateVCs(id: Identifier): Seq[VC] = {
    inox.Bench.time("generating postconditions", generatePostconditions(id)) ++
    inox.Bench.time("generating preconditions", generatePreconditions(id)) ++
    inox.Bench.time("generating correctness conditions", generateCorrectnessConditions(id))
  }

  def generatePostconditions(id: Identifier): Seq[VC]
  def generatePreconditions(id: Identifier): Seq[VC]
  def generateCorrectnessConditions(id: Identifier): Seq[VC]

  protected def sizeLimit(s: String, limit: Int) = {
    require(limit > 3)
    // Crop the call to display it properly

    val res = s.takeWhile(_ != '\n').take(limit)
    if (res == s) {
      res
    } else {
      res + " ..."
    }
  }
}
