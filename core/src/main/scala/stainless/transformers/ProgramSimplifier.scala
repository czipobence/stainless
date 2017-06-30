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

  private def transformVC(f: Expr => Expr)(vc: VC): VC =
    verification.VC(f(vc.condition), vc.fd, vc.kind).setPos(vc.getPos)
  
  private def transformFD(f: Expr => Expr)(fd: FunDef): FunDef =
    fd.copy(fullBody = f(fd.fullBody))
  

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
      case a@Assert(_, _, body) => Some(body.copiedFrom(a))
      case _ => None
    }, applyRec=true)(e)
  })


  private def removeAssertsAndRequires(funs: Map[Identifier, FunDef]): Map[Identifier, FunDef] = {

    funs.mapValues { fd =>
      val newBody = exprOps.preMap({
        case Assert(_, _, body) => Some(body)
        case Require(_, body) => Some(body)
        case _ => None
      }, applyRec = true)(fd.fullBody)

      fd.copy(fullBody = newBody)
    }
  }

  private def removeIndex[T](s: Seq[T], i: Int): Seq[T] =
    s.zipWithIndex.filter{ case (t,j) => j != i }.map(_._1)

  private def removeIndices[T](init: Seq[T], is: List[Int]): Seq[T] =
    is.foldLeft(init) { case (s, i) => removeIndex(s,i) }

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

  private def removeParameters(e: Expr, parametersToRemove: Map[Identifier, List[Int]]): Expr = {
    import trees._

    exprOps.postMap {
      case fi@FunctionInvocation(id, tps, args) =>
        Some(FunctionInvocation(
          id,
          tps,
          removeIndices(args, parametersToRemove.getOrElse(id, Nil))).copiedFrom(fi))
      case _ =>
        None
    }(e)
  }

  private def removeParameters(vc: VC, parametersToRemove: Map[Identifier, List[Int]]): VC =
    transformVC(removeParameters(_, parametersToRemove))(vc)

  private def removeParameter(fd: FunDef, id: Identifier, parameterToRemove: Int): FunDef = {
    fd.copy(fullBody = removeParameter(fd.fullBody, id, parameterToRemove))
  }

  def transform(syms: Symbols, vcs: Seq[VC]): (Symbols, Seq[VC]) = {

    val noassertFuns = removeAssertsAndRequires(syms.functions)
    val noassertVCs: Seq[VC] = vcs.map { vc => transformVC(removeAsserts)(vc) }

    def loop( funs: Map[Identifier, FunDef], 
              toVisit: Set[Identifier], 
              modifiers: Map[Identifier, List[Int]])
              : (Map[Identifier, FunDef], Map[Identifier, List[Int]]) = {
      if (toVisit.isEmpty) (funs, modifiers)
      else {

        val id = toVisit.head
        val fd = funs(id)
        if (fd.flags.exists(flag => flag match {
          case Extern => true
          case Annotation("library", _) => true
          case _ => false
        })) loop(funs, toVisit.tail, modifiers)
        else {
          val freeVariables = exprOps.variablesOf(fd.fullBody).map(v => v.id)
          fd.params.zipWithIndex.find { case (vd,_) => !freeVariables.contains(vd.id) } match {
            case Some((vd,i)) =>
              val calls = inox.Bench.time("getting callers", callers(fd).map(_.id))
              
              val funs2 = calls.foldLeft(funs) { case (funDefs, id2) =>
                val fd2 = funs(id2)
                val newFD2 = removeUnusedLets(removeParameter(fd2, id, i))
                funDefs.updated(fd2.id, newFD2)
              }
              val funs3 = funs2.updated(id, funs2(id).copy(
                params = removeIndex(funs2(id).params, i)
              ))
              val newModifiers = modifiers.updated(id, modifiers.getOrElse(id, Nil) :+ i)
              
              val newFD = funs3(id)
              val tempSymbols = NoSymbols.withFunctions(funs3.values.toSeq).withADTs(syms.adts.values.toSeq)

              loop(funs3, toVisit.tail ++ calls, newModifiers)
            case None =>
              loop(funs, toVisit.tail, modifiers)
         }
        }
      }
    }

    val (funs, modifiers) = loop(noassertFuns, syms.functions.values.map(_.id).toSet, Map())
    val newSyms = NoSymbols.withFunctions(funs.values.toSeq).withADTs(syms.adts.values.toSeq)
    
    (newSyms, noassertVCs.map(vc => removeUnusedLets(removeParameters(vc, modifiers))))
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