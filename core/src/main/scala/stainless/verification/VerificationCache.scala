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

  def buildDependencies(vc: VC): SubProgram = {
    new inox.Program {
      val trees: program.trees.type = program.trees
      val symbols = NoSymbols
      val ctx = program.ctx
    }
  }

  // case class CompleteVC(funs: Map[String,String], programADTs: Map[String,(String,String)], vcs: Set[String]) extends Serializable {
  //   def contains(vc: VC, program: self.program.type): Boolean = {
  //     val vcString = vc.condition.serialize
  //     vcs.contains(vcString) && {

  //       var adts = Set[(Identifier,ADTDefinition)]()

  //       inox.Bench.time("gathering adts", {
  //         new TreeTraverser {
  //           override def traverse(tpe: Type): Unit = {
  //             tpe match {
  //               case adt: ADTType =>
  //                 val id = adt.id
  //                 val a = getADT(adt.id)
  //                 adts += ((id,a))
  //               case _ => ()
  //             }
  //             super.traverse(tpe)
  //           }
  //         }.traverse(vc.condition)
  //       })

  //       val adtInvariants: Set[FunDef] = adts.flatMap(_._2.invariant)
  //       val invariantsBodies = adtInvariants.map(_.fullBody)

  //       val callees = inox.Bench.time("getting transitive callees", {
  //         (invariantsBodies + vc.condition).flatMap(e =>
  //           exprOps.functionCallsOf(e).flatMap(fi => transitiveCallees(fi.tfd.fd) + fi.tfd.fd)
  //         )
  //       })

  //       ctx.reporter.synchronized {
  //         ctx.reporter.debug("Checking containment of VC")
  //         ctx.reporter.debug(vc)
  //         ctx.reporter.debug("Program functions for the VC")
  //         for (fd <- callees) {
  //           ctx.reporter.debug(fd)
  //           ctx.reporter.debug("\n\n")
  //         }
  //         ctx.reporter.debug("ADT definitions for the VC")
  //         for (a <- adts) {
  //           ctx.reporter.debug(a)
  //           ctx.reporter.debug("\n\n")
  //         }
  //       }


  //       adts.forall {
  //         case (id,a) =>
  //           val serializedID = id.serialize
  //           programADTs.contains(serializedID) && programADTs(serializedID) == a.serialize
  //       } &&
  //       callees.forall { fd =>
  //         val serializedID = fd.id.serialize
  //         funs.contains(serializedID) && funs(serializedID) == fd.serialize
  //       }

  //     }
  //   }
  // }


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

    val sp = inox.Bench.time("building dependencies", buildDependencies(vc))
    val canonic = transformers.Canonization.canonize(sp)
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