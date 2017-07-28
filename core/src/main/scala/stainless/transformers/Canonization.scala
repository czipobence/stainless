/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

trait Canonization { selfcanonize =>

  val trees: stainless.ast.Trees
  val s: trees.type = trees
  val t: trees.type = trees

  import trees._

  type VC = verification.VC[trees.type]

  def transform(syms: s.Symbols, vc: VC): (t.Symbols, VC) = {
    var localCounter = 0
    var renaming: Map[Identifier,Identifier] = Map()

    def addRenaming(id: Identifier): Unit = {
      if (!renaming.contains(id)) {
        val newId = new Identifier("x",localCounter,0)
        renaming += ((id, newId))
      }
    }

    object idTransformer extends inox.ast.TreeTransformer {
      val s: selfcanonize.trees.type = selfcanonize.trees
      val t: selfcanonize.trees.type = selfcanonize.trees

      def transform(id: Identifier): Identifier = {
        addRenaming(id)
        renaming(id)
      }

      override def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = {
        (transform(id), transform(tpe))
      }
    }

    
    verification.VerificationCache.synchronized {
      println("Canonizing")
      println(vc.condition)
      println("End Condition")
    }
    val newVCBody = idTransformer.transform(vc.condition)

    val newFundefs = syms.functions.values.map { fd =>
      new FunDef(
        idTransformer.transform(fd.id),
        fd.tparams,
        fd.params.map(idTransformer.transform),
        fd.returnType,
        idTransformer.transform(fd.fullBody),
        fd.flags
      ).copiedFrom(fd)
    }

    val newADTs = syms.adts.values.map { adt => 
      verification.VerificationCache.synchronized {
        println("YAY====")
        println("matching: " + adt)
        println("YAY====")
      }
      adt match {
      case sort: s.ADTSort => new t.ADTSort(
        idTransformer.transform(sort.id),
        sort.tparams map idTransformer.transform,
        sort.cons,
        sort.flags map idTransformer.transform
      )

      case cons: s.ADTConstructor => 
        verification.VerificationCache.synchronized {
          println("YO====")
          println("I just found: " + cons)
          println("YO====")
        }
        new t.ADTConstructor(
          idTransformer.transform(cons.id),
          cons.tparams map idTransformer.transform,
          cons.sort,
          cons.fields map idTransformer.transform,
          cons.flags map idTransformer.transform
        )
    }}

    val newSyms = NoSymbols.withFunctions(newFundefs.toSeq).withADTs(newADTs.toSeq)

    (newSyms, verification.VC[trees.type](
      newVCBody,
      idTransformer.transform(vc.fd),
      vc.kind
    ))
  }
}


object Canonization {
  def canonize(thetrees: stainless.ast.Trees)
              (p: inox.Program { val trees: thetrees.type }, vc: verification.VC[thetrees.type]): 
                inox.Program { val trees: thetrees.type } = {
    object canonizer extends Canonization {
      override val trees: p.trees.type = p.trees
    }

    val (newSymbols, newVC) = canonizer.transform(p.symbols, vc)
    new inox.Program {
      val trees: p.trees.type = p.trees
      val symbols = newSymbols
      val ctx = p.ctx
    }
  }
}