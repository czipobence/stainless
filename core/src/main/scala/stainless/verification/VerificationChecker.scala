/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.solvers._

import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

object optParallelVCs extends inox.FlagOptionDef("parallelvcs", false)
object optFailEarly extends inox.FlagOptionDef("failearly", false)
object optVCCache extends inox.FlagOptionDef("vccache", false)

object DebugSectionVerification extends inox.DebugSection("verification")

trait VerificationChecker { self =>
  val program: Program
  val options: inox.Options

  private lazy val parallelCheck = options.findOptionOrDefault(optParallelVCs)
  private lazy val failEarly = options.findOptionOrDefault(optFailEarly)
  private lazy val vccache = options.findOptionOrDefault(optVCCache)
  private lazy val cacheFile = "vccache.bin"

  import program._
  import program.trees._
  import program.symbols._
  import CallGraphOrderings._

  implicit val debugSection = DebugSectionVerification

  type VC = verification.VC[program.trees.type]
  val VC = verification.VC

  type VCStatus = verification.VCStatus[program.Model]

  type VCResult = verification.VCResult[program.Model]
  val VCResult = verification.VCResult

  protected def getTactic(fd: FunDef): Tactic { val program: self.program.type }
  protected def getFactory: SolverFactory {
    val program: self.program.type
    type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
  }

  private def defaultStop(res: VCResult): Boolean = if (failEarly) res.status != VCStatus.Valid else false

  def verify(funs: Seq[Identifier], stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
    val sf = ctx.options.findOption(inox.optTimeout) match {
      case Some(to) => getFactory.withTimeout(to)
      case None => getFactory
    }

    try {
      ctx.reporter.debug("Generating Verification Conditions...")
      val vcs = inox.Bench.time("generating vcs", generateVCs(funs))

      ctx.reporter.debug("Checking Verification Conditions...")
      inox.Bench.time("checking vcs", checkVCs(vcs, sf, stopWhen))
    } finally {
      sf.shutdown()
    }
  }

  def generateVCs(funs: Seq[Identifier]): Seq[VC] = {
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
    if (vccache && new java.io.File(cacheFile).exists) {
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

  private lazy val unknownResult: VCResult = VCResult(VCStatus.Unknown, None, None)

  def checkVCs(vcs: Seq[VC], sf: SolverFactory { val program: self.program.type }, stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
    var stop = false

    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap
    val verifiedVCs = inox.Bench.time("getVerifiedVCS", getVerifiedVCs())

    def checkVCWithCache(vc: VC, sf: SolverFactory { val program: self.program.type }) = inox.Bench.time("check vc with cache", {
      if (vccache && verifiedVCs.contains(vc,program)) {
        ctx.reporter.synchronized {
          ctx.reporter.debug("The following VC has already been verified:")
          ctx.reporter.debug(vc)
          ctx.reporter.debug("--------------")
        }
        VCResult(VCStatus.Valid, None, Some(0))
      } 
      else
        inox.Bench.time("checking VC", checkVC(vc,sf))
    })

    // scala doesn't seem to have a nice common super-type of vcs and vcs.par, so these
    // two quasi-identical pieces of code have to remain separate...
    val results = if (parallelCheck) {
      for (vc <- vcs.par if !stop && !ctx.interruptManager.isInterrupted) yield {
        val res = checkVCWithCache(vc, sf)
        if (ctx.interruptManager.isInterrupted) ctx.interruptManager.reset()
        stop = stopWhen(res)
        vc -> res
      }
    } else {
      for (vc <- vcs if !stop && !ctx.interruptManager.isInterrupted) yield {
        val res = checkVCWithCache(vc, sf)
        if (ctx.interruptManager.isInterrupted) ctx.interruptManager.reset()
        stop = stopWhen(res)
        vc -> res
      }
    }

    if (vccache) {
      inox.Bench.time("writing vc", {
        val newVerifiedVCs: Set[String] = Set[String]() ++
          inox.Bench.time("serializing VCs", results.
            filter { case (vc, res) => res.isValid }.
            map { case (vc, res) => vc.condition.serialize })

        val funs = inox.Bench.time("serializing functions", program.symbols.functions.map { case (k,v) => (k.serialize,v.serialize) })
        val adts = inox.Bench.time("serializing adts", program.symbols.adts.map { case (k,v) => (k.serialize,v.serialize) })
        val v = VerifiedVCs(funs, adts, newVerifiedVCs)

        writeVerifiedVCs(v)
      })
    }

    initMap ++ results
  }

  private def removeUnusedLets(e: Expr): Expr = {
    exprOps.postMap({
      case Let(vd,_,body) =>
        if (exprOps.variablesOf(body).contains(vd.toVariable)) None
        else Some(body)
      case _ => None
    }, applyRec=true)(e)
  }

  private def removeAsserts(e: Expr): Expr = {
    exprOps.preMap({
      case Assert(_, _, body) => Some(body)
      case _ => None
    }, applyRec=true)(e)
  }

  private def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }): VCResult = {
    import SolverResponses._
    val s = sf.getNewSolver

    try {
      val cond_aux = inox.Bench.time("simplifyLets", simplifyLets(vc.condition))
      val cond = inox.Bench.time("removals", removeUnusedLets(removeAsserts(cond_aux)))
      ctx.reporter.synchronized {
        ctx.reporter.info(s" - Now considering '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
        ctx.reporter.debug(cond.asString)
        ctx.reporter.debug("Solving with: " + s.name)
      }

      val timer = ctx.timers.verification.start()

      val vcres = try {
        s.assertCnstr(Not(cond))

        val res = inox.Bench.time("model checking", s.check(Model))

        val time = timer.stop()

        res match {
          case _ if ctx.interruptManager.isInterrupted =>
            VCResult(VCStatus.Cancelled, Some(s), Some(time))

          case Unknown =>
            VCResult(s match {
              case ts: inox.solvers.combinators.TimeoutSolver => ts.optTimeout match {
                case Some(t) if t < time => VCStatus.Timeout
                case _ => VCStatus.Unknown
              }
              case _ => VCStatus.Unknown
            }, Some(s), Some(time))

          case Unsat =>
            VCResult(VCStatus.Valid, s.getResultSolver, Some(time))

          case SatWithModel(model) =>
            VCResult(VCStatus.Invalid(model), s.getResultSolver, Some(time))
        }
      } catch {
        case u: Unsupported =>
          val t = timer.selfTimer.get
          val time = if (t.isRunning) t.stop else t.runs.last
          ctx.reporter.warning(u.getMessage)
          VCResult(VCStatus.Unsupported, Some(s), Some(time))
      }

      ctx.reporter.synchronized {
        if (parallelCheck)
          ctx.reporter.info(s" - Result for '${vc.kind}' VC for ${vc.fd} @${vc.getPos}:")

        vcres.status match {
          case VCStatus.Valid =>
            ctx.reporter.info(" => VALID")

          case VCStatus.Invalid(cex) =>
            ctx.reporter.warning(" => INVALID")
            ctx.reporter.warning("Found counter-example:")
            ctx.reporter.warning("  " + cex.asString.replaceAll("\n", "\n  "))

          case status =>
            ctx.reporter.warning(" => " + status.name.toUpperCase)
        }
      }

      vcres
    } finally {
      s.free()
    }
  }
}

object VerificationChecker {
  def verify(p: StainlessProgram, opts: inox.Options)
            (funs: Seq[Identifier]): Map[VC[p.trees.type], VCResult[p.Model]] = {
    object checker extends VerificationChecker {
      val program: p.type = p
      val options = opts

      val defaultTactic = DefaultTactic(p)
      val inductionTactic = InductionTactic(p)

      protected def getTactic(fd: p.trees.FunDef) =
        if (fd.flags contains "induct") {
          inductionTactic
        } else {
          defaultTactic
        }

      val simpleP = new inox.Program {
        val trees = p.trees
        val symbols = transformers.ProgramSimplifier.transform(p.symbols)
        val ctx = p.ctx
      }

      protected def getFactory = solvers.SolverFactory.apply(p, opts)
    }

    checker.verify(funs)
  }

  def verify(p: StainlessProgram)(funs: Seq[Identifier]): Map[VC[p.trees.type], VCResult[p.Model]] = {
    verify(p, p.ctx.options)(funs)
  }
}
