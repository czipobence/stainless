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
      val vcs = Bench.time("generating vcs", generateVCs(funs))

      ctx.reporter.debug("Checking Verification Conditions...")
      Bench.time("checking vcs", checkVCs(vcs, sf, stopWhen))
    } finally {
      sf.shutdown()
    }
  }

  def generateVCs(funs: Seq[Identifier]): Seq[VC] = {
    val vcs: Seq[VC] = (for (id <- funs) yield {
      val fd = getFunction(id)
      val tactic = getTactic(fd)

      if (fd.body.isDefined) {
        Bench.time("generating", tactic.generateVCs(id))
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

  // Self-Contained VC: stores all functions definitions needed for this VC
  // FIXME: for soundness, we should also store all subtypes of the ADTs
  // FIXME: e.g. caching e.isInstanceOf(A) || e.isInstanceOf(B) is not sound if we add "case class C extends T"
  // FIXME: with e of type T, and case class A extends T, and case class B extends T.
  type SCVC = String
  def selfContained(vc: VC, program: self.program.type): SCVC = {
    val callees = exprOps.functionCallsOf(vc.condition).flatMap(fi => transitiveCallees(fi.tfd.fd) + fi.tfd.fd)
    val types: Set[String] = exprOps.collect {
      case e => e.getType match {
        case a @ ADTType(_,_) => Set(a.getADT.toString)
        case _ => Set[String]()
      }
    } (vc.condition)

    vc.condition.toString +
      "\n\nFunction Definitions\n\n" +
      callees.toList.sorted.mkString("\n\n") +
      "\n\nType Definitions:\n\n" +
      types.toList.sorted.mkString("\n\n")
  }

  def getVerifiedVCs(): Set[SCVC] = {
    if (new java.io.File(cacheFile).exists) {
      val ois = new ObjectInputStream(new FileInputStream(cacheFile))
      val verifiedVCs = ois.readObject.asInstanceOf[Set[SCVC]]
      ois.close()
      verifiedVCs
    }
    else Set()
  }

  def writeVerifiedVCs(vcs: Set[SCVC]) = {
    val oos = new ObjectOutputStream(new FileOutputStream(cacheFile))
    oos.writeObject(vcs)
    oos.close()
  }

  private lazy val unknownResult: VCResult = VCResult(VCStatus.Unknown, None, None)

  def checkVCs(vcs: Seq[VC], sf: SolverFactory { val program: self.program.type }, stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
    var stop = false

    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap
    val verifiedVCs: Set[SCVC] = if (vccache) Bench.time("getVerifiedVCS", getVerifiedVCs()) else Set()

    println("the whole program")

    println(program)

    println("thank you")


    for (scvc <- verifiedVCs) {
      println("I have already verified the following VC:")
      println(scvc)
      println("==============================================")
    }

    def checkVCWithCache(vc: VC, sf: SolverFactory { val program: self.program.type }) = {
      if (vccache && verifiedVCs.contains(selfContained(vc,program)))
        VCResult(VCStatus.Valid, None, Some(0))
      else
        Bench.time("checking VC", checkVC(vc,sf))
    }

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
      val newVerifiedVCs: Set[SCVC] = Set[SCVC]() ++
        results.
          filter { case (vc, res) => res.isValid }.
          map { case (vc, res) => selfContained(vc,program) }

      writeVerifiedVCs(newVerifiedVCs)
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
      val cond_aux = Bench.time("simplifyLets", simplifyLets(vc.condition))
      val cond = Bench.time("removals", removeUnusedLets(removeAsserts(cond_aux)))
      ctx.reporter.synchronized {
        ctx.reporter.info(s" - Now considering '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
        ctx.reporter.debug(cond.asString)
        ctx.reporter.debug("Solving with: " + s.name)
      }

      val timer = ctx.timers.verification.start()

      val vcres = try {
        s.assertCnstr(Not(cond))

        val res = Bench.time("model checking", s.check(Model))

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

      val time = timer.stop()

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

      protected def getFactory = solvers.SolverFactory.apply(p, opts)
    }

    checker.verify(funs)
  }

  def verify(p: StainlessProgram)(funs: Seq[Identifier]): Map[VC[p.trees.type], VCResult[p.Model]] = {
    verify(p, p.ctx.options)(funs)
  }
}
