/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

trait Canonization extends inox.ast.SymbolTransformer { self =>

  val trees: inox.ast.Trees
  val s: trees.type = trees
  val t: trees.type = trees

  def transform(syms: s.Symbols): t.Symbols = syms
}


object Canonization {
  def canonize(p: inox.Program): inox.Program { val trees: p.trees.type } = {
    object canonizer extends Canonization {
      override val trees: p.trees.type = p.trees
    }
    new inox.Program {
      val trees: p.trees.type = p.trees
      val symbols = canonizer.transform(p.symbols)
      val ctx = p.ctx
    }
  }
}