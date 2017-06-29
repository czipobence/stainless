/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

trait ProgramSimplifier { self =>

  val program: StainlessProgram

  import program._
  import program.symbols._
  import program.trees._

  import CallGraphOrderings._

  type VC = verification.VC[trees.type]

  private def transformVC(f: Expr => Expr)(vc: VC): VC = {
    verification.VC(f(vc.condition), vc.fd, vc.kind)
  }
  private def transformFD(f: Expr => Expr)(fd: FunDef): FunDef = {
    fd.copy(fullBody = f(fd.fullBody))
  }

  private def removeUnusedLets(e: Expr): Expr = {
    exprOps.postMap({
      case Let(vd,_,body) =>
        if (exprOps.variablesOf(body).contains(vd.toVariable)) None
        else Some(body)
      case _ => None
    }, applyRec=true)(e)
  }

  private def removeUnusedLets(vc: VC): VC = inox.Bench.time("removing unused lets vc", transformVC(removeUnusedLets)(vc))
  private def removeUnusedLets(fd: FunDef): FunDef = inox.Bench.time("removing unused lets fd", transformFD(removeUnusedLets)(fd))

  private def removeAsserts(e: Expr): Expr = inox.Bench.time("removing asserts", {
    exprOps.preMap({
      case Assert(_, _, body) => Some(body)
      case _ => None
    }, applyRec=true)(e)
  })


  private def removeAssertsAndRequires(syms: Symbols): Symbols = {

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

  private def removeIndex[T](s: Seq[T], i: Int): Seq[T] =
    s.zipWithIndex.filter{ case (t,j) => j != i }.map(_._1)

  private def removeParameter(e: Expr, id: Identifier, parameterToRemove: Int): Expr = {
    import trees._

    exprOps.postMap {
      case fi@FunctionInvocation(id2, tps, args) if (id2 == id) =>
        Some(FunctionInvocation(
          id,
          tps,
          removeIndex(args, parameterToRemove)).copiedFrom(fi))
      case _ =>
        None
    }(e)
  }

  private def removeParameter(vc: VC, id: Identifier, parameterToRemove: Int): VC = {
    verification.VC(removeParameter(vc.condition, id, parameterToRemove), vc.fd, vc.kind)
  }

  private def removeParameter(fd: FunDef, id: Identifier, parameterToRemove: Int): FunDef = {
    fd.copy(fullBody = removeParameter(fd.fullBody, id, parameterToRemove))
  }

  def transform(syms: Symbols, vcs: Seq[VC]): (Symbols, Seq[VC]) = {

    println("simplifying program")
//    println(syms)

    val noassertSymbs = removeAssertsAndRequires(syms)
    val noassertVCs = vcs.map(transformVC(removeAsserts))

    println("======================")
    println("removed asserts")
//    println(noassertSymbs)

    def loop(syms: Symbols, vcs: Seq[VC]): (Symbols, Seq[VC]) = {
      println("======================")
      println("looping")
//      println(syms)
      for ((id, fd) <- syms.functions if (!fd.flags.exists(flag => flag match {
        case Extern => true
        case Annotation("library", _) => true
        case _ => false
      }))) {
        val freeVariables = exprOps.variablesOf(fd.fullBody).map(v => v.id)
        fd.params.zipWithIndex.find { case (vd,_) => !freeVariables.contains(vd.id) } match {
          case Some((vd,i)) =>
            println(fd.flags)
            println("Removing %s at index %s from:".format(vd,i))
            println(fd)
            val calls = inox.Bench.time("getting callers", callers(fd))
            inox.Bench.reportS()
            val funs2 = calls.foldLeft(syms.functions) {
              case (funDefs, fd2) =>
                funDefs.updated(fd2.id, removeUnusedLets(removeParameter(fd2, id, i)))
            }
            val funs3 = funs2.updated(id, funs2(id).copy(params = removeIndex(funs2(id).params, i)))
            val newVCs = vcs.map((vc: VC) => removeUnusedLets(removeParameter(vc, id, i)))
            val newSyms = NoSymbols.withFunctions(funs3.values.toSeq).withADTs(syms.adts.values.toSeq)
            loop(newSyms, newVCs)
          case None => ()
        }
      }
      (syms, vcs)
    }

    loop(noassertSymbs, noassertVCs)
  }
}


object ProgramSimplifier {

  def simplify(p: StainlessProgram)(vcs: Seq[verification.VC[p.trees.type]]): (StainlessProgram, Seq[verification.VC[p.trees.type]]) = {
    object simplifier extends ProgramSimplifier {
      override val program = p
    }
    val (syms2, vcs2) = inox.Bench.time("simplifier", simplifier.transform(p.symbols, vcs))
    val p2 = new inox.Program {
      val trees = p.trees
      val symbols = syms2
      val ctx = p.ctx
    }

    (p2, vcs2)
  }
}