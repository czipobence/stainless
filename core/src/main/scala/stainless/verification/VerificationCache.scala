/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification


import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

import inox.solvers.SolverFactory

trait VerificationCache extends VerificationChecker { self =>

  import program._
  import program.symbols._
  import program.trees._

  type SubProgram = inox.Program { val trees: program.trees.type }

  val uniq = new PrinterOptions(printUniqueIds = true)

  def buildDependencies(vc: VC): SubProgram = {

    var adts = Set[(Identifier,ADTDefinition)]()
    var fundefs = Set[FunDef]()
    var traversedExpr = Set[Expr]()
    var traversedTypes = Set[Type]()

    val traverser = new TreeTraverser {
      override def traverse(e: Expr): Unit = {
        if (!traversedExpr.contains(e)) {
          traversedExpr += e
          // ctx.reporter.synchronized {
          //   ctx.reporter.debug("TRAVERSING AN EXPRESSION")
          //   ctx.reporter.debug(e)
          //   ctx.reporter.debug("--------------")
          // }
          val callees = inox.Bench.time("getting transitive callees", {
            exprOps.functionCallsOf(e).flatMap(fi => transitiveCallees(fi.tfd.fd) + fi.tfd.fd)
          })
          fundefs = fundefs ++ callees
          super.traverse(e)
        }
      }
      override def traverse(tpe: Type): Unit = {
        if (!traversedTypes.contains(tpe)) {
          traversedTypes += tpe
          tpe match {
            case adt: ADTType =>
              val id = adt.id
              val a = getADT(adt.id)
              a.invariant.map(inv => traverse(inv.fullBody))
              adts += ((id,a))
            case _ => ()
          }
          super.traverse(tpe)
        }
      }
    }

    traverser.traverse(vc.condition)

    new inox.Program {
      val trees: program.trees.type = program.trees
      val symbols = NoSymbols.withFunctions(fundefs.toSeq).withADTs(adts.map(_._2).toSeq)
      val ctx = program.ctx
    }
  }


  // def getVerifiedVCs(): VerifiedVCs = {
  //   if (new java.io.File(cacheFile).exists) {
  //     val ois = new ObjectInputStream(new FileInputStream(cacheFile))
  //     val (funs,adts,vcs) = ois.readObject.asInstanceOf[(Map[String,String], Map[String,(String,String)], Set[String])]
  //     ois.close()
  //     VerifiedVCs(funs,adts,vcs)
  //   }
  //   else {
  //     VerifiedVCs(Map(),Map(),Set())
  //   }
  // }

  // def writeVerifiedVCs(v: VerifiedVCs) = {
  //   val oos = new ObjectOutputStream(new FileOutputStream(cacheFile))
  //   oos.writeObject((v.funs, v.programADTs, v.vcs))
  //   oos.close()
  // }

  // val verifiedVCs = inox.Bench.time("getVerifiedVCS", getVerifiedVCs())

  override def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }) = {
    import VerificationCache._

    val sp: SubProgram = inox.Bench.time("building dependencies", buildDependencies(vc))
    val canonic = transformers.Canonization.canonize(sp.trees)(sp, vc)
    VerificationCache.synchronized {
      println("Dependencies of: " + vc.condition.asString(uniq))
      println("================")
      println(sp.asString)
      println("================")
      println("Canonic Form:")
      println(canonic.asString)
    }
    if (vccache.contains(canonic)) {
      ctx.reporter.synchronized {
        ctx.reporter.debug("The following VC has already been verified:")
        ctx.reporter.debug(vc)
        ctx.reporter.debug("--------------")
      }
      VCResult(VCStatus.Valid, None, Some(0))
    }
    else {
      val result = inox.Bench.time("checking VC", super.checkVC(vc,sf))
      vccache += ((canonic, ()))
      result
    }
  }

}

object VerificationCache {
  var vccache: scala.collection.concurrent.Map[Program,Unit] =
    scala.collection.concurrent.TrieMap()
}