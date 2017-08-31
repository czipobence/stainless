/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait VerificationGenerator { self =>
  val program: Program

  import program._
  import program.symbols._
  import program.trees._
  import CallGraphOrderings._

  type VC = verification.VC[program.trees.type]

  protected def getTactic(fd: FunDef): Tactic { val program: self.program.type }

<<<<<<< HEAD

=======
>>>>>>> 703393b9ba32088ec2fa40754cd94a65f09e1d4a
  def generateVCs(funs: Seq[Identifier]): Seq[VC] = {
    val vcs: Seq[VC] = (for (id <- funs) yield {
      val fd = getFunction(id)
      val tactic = getTactic(fd)

      if (fd.body.isDefined) {
<<<<<<< HEAD
        inox.Bench.time("generating VCs", tactic.generateVCs(id))
=======
        tactic.generateVCs(id)
>>>>>>> 703393b9ba32088ec2fa40754cd94a65f09e1d4a
      } else {
        Nil
      }
    }).flatten

    vcs.sortBy(vc => (getFunction(vc.fd),
      if (vc.kind.underlying == VCKind.Precondition) 0
      else if (vc.kind.underlying == VCKind.Assert) 1
      else 2
    ))
  }

}

object VerificationGenerator {

  def gen(p: StainlessProgram)(funs: Seq[Identifier]): Seq[VC[p.trees.type]] = {
    object generator extends VerificationGenerator {
      val program: p.type = p

      val defaultTactic = DefaultTactic(p)
      val inductionTactic = InductionTactic(p)

      protected def getTactic(fd: p.trees.FunDef) =
        if (fd.flags contains "induct") {
          inductionTactic
        } else {
          defaultTactic
        }
    }
    generator.generateVCs(funs)
  }

<<<<<<< HEAD
}
=======
}
>>>>>>> 703393b9ba32088ec2fa40754cd94a65f09e1d4a
