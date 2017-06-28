/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

trait ProgramSimplifier extends inox.ast.SymbolTransformer { self =>

  val trees: ast.Trees
  val s: trees.type = trees
  val t: trees.type = trees

  type VC = verification.VC[trees.type]

  val mutChanges

  def removeAssertsAndRequire(syms: s.Symbols): t.Symbols = {
    import s._

    val newFunctions = syms.functions.values.map { fd =>
      val newBody = exprOps.preMap({
        case Assert(_, _, body) => Some(body)
        case Require(_, body) => Some(body)
        case _ => None
      }, applyRec = true)(fd.fullBody)

      fd.copy(fullBody = newBody)
    }.toSeq

    NoSymbols.withFunctions(newFunctions).withADTs(syms.adts.values.toSeq)
  }

  def transform(syms: s.Symbols): t.Symbols = {
    import s._
    import stainless.trees.exprOps._

    val noassertSymbs = removeAssertsAndRequire(syms)
    noassertSymbs
  }

  def transformAndManifest(): (t.Symbols, )

  def transformVCs(vcs1: Seq²VC): Seq^VC
}
