/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

trait Canonization { selfcanonize =>

  val trees: stainless.ast.Trees
  lazy val s: selfcanonize.trees.type = selfcanonize.trees
  lazy val t: selfcanonize.trees.type = selfcanonize.trees

  import selfcanonize.trees._

  type VC = verification.VC[trees.type]

  def transform(syms: s.Symbols, vc: VC): (t.Symbols, Expr) = {
    var localCounter = 0
    var renaming: Map[Identifier,Identifier] = Map()

    def addRenaming(id: Identifier): Unit = {
      if (!renaming.contains(id)) {
        val newId = new Identifier("x",localCounter,localCounter)
        localCounter = localCounter + 1
        renaming += ((id, newId))
      }
    }

    object idTransformer extends inox.ast.TreeTransformer {
      val s: selfcanonize.trees.type = selfcanonize.trees
      val t: selfcanonize.trees.type = selfcanonize.trees

      override def transform(id: Identifier): Identifier = {
        addRenaming(id)
        renaming(id)
      }
    }

    val newVCBody = idTransformer.transform(vc.condition)

    /** Should be changed so that functions are traversed in the order they
      * appear in `vc.condition`
      */

    val newFundefs = syms.functions.values.map { fd =>
      new FunDef(
        idTransformer.transform(fd.id),
        fd.tparams map idTransformer.transform,
        fd.params.map(idTransformer.transform),
        idTransformer.transform(fd.returnType),
        idTransformer.transform(fd.fullBody),
        fd.flags
      ).copiedFrom(fd)
    }

    val newADTs = syms.adts.values.map { adt => adt match {
      case sort: s.ADTSort => new t.ADTSort(
        idTransformer.transform(sort.id),
        sort.tparams map idTransformer.transform,
        sort.cons map idTransformer.transform,
        sort.flags map idTransformer.transform
      ).copiedFrom(adt)

      case cons: s.ADTConstructor => new t.ADTConstructor(
        idTransformer.transform(cons.id),
        cons.tparams map idTransformer.transform,
        cons.sort map idTransformer.transform,
        cons.fields map idTransformer.transform,
        cons.flags map idTransformer.transform
      ).copiedFrom(adt)
    }}
    val newSyms = NoSymbols.withFunctions(newFundefs.toSeq).withADTs(newADTs.toSeq)

    (newSyms, newVCBody)
  }
}


object Canonization {
  def canonize(thetrees: stainless.ast.Trees)
              (p: inox.Program { val trees: thetrees.type }, vc: verification.VC[thetrees.type]): 
                (p.trees.Symbols, thetrees.Expr)  = {
    object canonizer extends Canonization {
      override val trees: p.trees.type = p.trees
    }

    val (newSymbols, newVCBody) = canonizer.transform(p.symbols, vc)

    (newSymbols, newVCBody)
  }
}