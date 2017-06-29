/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

trait ProgramSimplifier { self =>

  val trees: ast.Trees
  val s: trees.type = trees
  val t: trees.type = trees

  type VC = verification.VC[trees.type]

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

  def transform(syms: s.Symbols): (t.Symbols, Map[Identifier,Set[Int]]) = {
    import s._
    import stainless.trees.exprOps._

    val noassertSymbs = removeAssertsAndRequire(syms)
    (noassertSymbs, Map())
  }
}


object ProgramSimplifier {
  def simplify(p: StainlessProgram): (StainlessProgram, Map[Identifier,Set[Int]]) = {
    object simplifier extends ProgramSimplifier {
      override val trees = p.trees
    }
    val (syms2, modifiers) = simplifier.transform(p.symbols)
    val p2 = new inox.Program {
      val trees = p.trees
      val symbols = syms2
      val ctx = p.ctx
    }
    (p2, modifiers)
  }

  def transformVCs[T](vcs1: Seq[VC[T]], parametersToRemove: Map[Identifier,Set[Int]]): Seq[VC[T]] = vcs1
}