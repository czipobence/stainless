/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification


import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

import inox.solvers.SolverFactory

object DebugSectionCache extends inox.DebugSection("cache")

trait VerificationCache extends VerificationChecker { self =>

  import program._
  import program.symbols._
  import program.trees._

  implicit val debugSectionCache = DebugSectionCache

  private lazy val cacheFile = "vccache.bin"


  implicit class SerializeFunDef(fd: FunDef) {
    val uniq = new PrinterOptions(printUniqueIds = true)
    def serialize(): String = fd.asString(uniq)
  }

  implicit class SerializeExpr(e: Expr) {
    val uniq = new PrinterOptions(printUniqueIds = true)
    def serialize(): String = e.asString(uniq)
  }

  implicit class SerializeADTDef(a: ADTDefinition) {
    val uniq = new PrinterOptions(printUniqueIds = true)
    def serialize(): (String,String) = ((a.asString(uniq), a.invariant.map(_.asString(uniq)).mkString))
  }

  implicit class SerializeIdentifier(id: Identifier) {
    val uniq = new PrinterOptions(printUniqueIds = true)
    def serialize(): String = id.asString(uniq)
  }




  // Self-Contained VCs: stores a set of verified VCs
  // We store every function definition. For adts, we store the ADT definition as well
  // the invariant.
  case class VerifiedVCs(funs: Map[String,String], programADTs: Map[String,(String,String)], vcs: Set[String]) extends Serializable {
    def contains(vc: VC, program: self.program.type): Boolean = {
      val vcString = vc.condition.serialize
      vcs.contains(vcString) && {

        var adts = Set[(Identifier,ADTDefinition)]()

        inox.Bench.time("gathering adts", {
          new TreeTraverser {
            override def traverse(tpe: Type): Unit = {
              tpe match {
                case adt: ADTType =>
                  val id = adt.id
                  val a = getADT(adt.id)
                  adts += ((id,a))
                case _ => ()
              }
              super.traverse(tpe)
            }
          }.traverse(vc.condition)
        })

        val adtInvariants: Set[FunDef] = adts.flatMap(_._2.invariant)
        val invariantsBodies = adtInvariants.map(_.fullBody)

        val callees = inox.Bench.time("getting transitive callees", {
          (invariantsBodies + vc.condition).flatMap(e =>
            exprOps.functionCallsOf(e).flatMap(fi => transitiveCallees(fi.tfd.fd) + fi.tfd.fd)
          )
        })

        ctx.reporter.synchronized {
          ctx.reporter.debug("Checking containment of VC")
          ctx.reporter.debug(vc)
          ctx.reporter.debug("Program functions for the VC")
          for (fd <- callees) {
            ctx.reporter.debug(fd)
            ctx.reporter.debug("\n\n")
          }
          ctx.reporter.debug("ADT definitions for the VC")
          for (a <- adts) {
            ctx.reporter.debug(a)
            ctx.reporter.debug("\n\n")
          }
        }


        adts.forall {
          case (id,a) =>
            val serializedID = id.serialize
            programADTs.contains(serializedID) && programADTs(serializedID) == a.serialize
        } &&
        callees.forall { fd =>
          val serializedID = fd.id.serialize
          funs.contains(serializedID) && funs(serializedID) == fd.serialize
        }

      }
    }
  }


  def getVerifiedVCs(): VerifiedVCs = {
    if (new java.io.File(cacheFile).exists) {
      val ois = new ObjectInputStream(new FileInputStream(cacheFile))
      val (funs,adts,vcs) = ois.readObject.asInstanceOf[(Map[String,String], Map[String,(String,String)], Set[String])]
      ois.close()
      VerifiedVCs(funs,adts,vcs)
    }
    else {
      VerifiedVCs(Map(),Map(),Set())
    }
  }

  def writeVerifiedVCs(v: VerifiedVCs) = {
    val oos = new ObjectOutputStream(new FileOutputStream(cacheFile))
    oos.writeObject((v.funs, v.programADTs, v.vcs))
    oos.close()
  }

  val verifiedVCs = inox.Bench.time("getVerifiedVCS", getVerifiedVCs())

  override def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }) = inox.Bench.time("check vc with cache", {
    if (verifiedVCs.contains(vc,program)) {
      ctx.reporter.synchronized {
        ctx.reporter.debug("The following VC has already been verified:")
        ctx.reporter.debug(vc)
        ctx.reporter.debug("--------------")
      }
      VCResult(VCStatus.Valid, None, Some(0))
    }
    else
      inox.Bench.time("checking VC", super.checkVC(vc,sf))
  })

  override def checkVCs(vcs: Seq[VC], sf: SolverFactory { val program: self.program.type }, stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
    val results = super.checkVCs(vcs,sf,stopWhen)

    inox.Bench.time(
    "writing vc", {
      val newVerifiedVCs: Set[String] =
        Set[String]() ++
        inox.Bench.time(
          "serializing VCs", results.
            filter { case (vc, res) => res.isValid }.
            map { case (vc, res) => vc.condition.serialize })

      val funs = inox.Bench.time("serializing functions", program.symbols.functions.map { case (k, v) => (k.serialize, v.serialize) })
      val adts = inox.Bench.time("serializing adts", program.symbols.adts.map { case (k, v) => (k.serialize, v.serialize) })
      val v = VerifiedVCs(funs, adts, newVerifiedVCs)

      writeVerifiedVCs(v)
    })
    results
  }

}