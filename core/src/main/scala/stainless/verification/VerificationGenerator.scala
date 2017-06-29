/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait VerificationGenerator { self =>
  val program: Program

  def generateVCs(funs: Seq[Identifier]): Seq[VC[self.program.trees.type]] = {
    val vcs: Seq[VC] = (for (id <- funs) yield {
      val fd = getFunction(id)
      val tactic = getTactic(fd)

      if (fd.body.isDefined) {
        inox.Bench.time("generating", tactic.generateVCs(id))
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

    def gen(p: StainlessProgram, opts: inox.Options)(funs: Seq[Identifier]): Seq[VC[p.trees.type]] = {
        generateVCs(funs)
    }

    def gen(p: StainlessProgram)(funs: Seq[Identifier]): Seq[VC[p.trees.type]] = {
        gen(p, p.ctx.options)(funs)
    }

}