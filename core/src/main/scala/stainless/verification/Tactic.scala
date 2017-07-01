/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait Tactic {
  val program: Program
  val description: String

  protected type VC = verification.VC[program.trees.type]
  protected def VC(cond: program.trees.Expr, id: Identifier, kind: VCKind, nonRemovable: Set[String] = Set()): VC = {
    // println("create VC with nonRemovable: " + nonRemovable)
    verification.VC(cond, id, kind, nonRemovable)
  }

  def generateVCs(id: Identifier): Seq[VC] = {
    inox.Bench.time("postconditions", generatePostconditions(id)) ++
    inox.Bench.time("preconditions", generatePreconditions(id)) ++
    inox.Bench.time("correctness", generateCorrectnessConditions(id))
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
