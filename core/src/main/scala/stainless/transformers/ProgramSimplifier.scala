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
    verification.VC(f(vc.condition), vc.fd, vc.kind, vc.nonRemovable).setPos(vc.getPos)
  
  private def transformFD(f: Expr => Expr)(fd: FunDef): FunDef =
    fd.copy(fullBody = f(fd.fullBody))
  

  private def removeUnusedLets(e: Expr, except: Set[String] = Set()): Expr = {
    exprOps.postMap({
      case Let(vd,_,body) =>
        if (exprOps.variablesOf(body).contains(vd.toVariable) ||
            inox.isPersistent(vd.id.name) ||
            except.contains(vd.id.name))
          None
        else { 
          // println("removing variable " + vd.id)
          // println("exceptions: " + except)
          Some(body)
        }
      case _ => None
    }, applyRec=true)(e)
  }
 
  private def removeUnusedLets(vc: VC): VC = inox.Bench.time("removing unused lets vc", {
    // println("removing unused lets from vc")
    // println(vc)
    // println("exceptions: " + vc.nonRemovable)
    transformVC((e: Expr) => removeUnusedLets(e, vc.nonRemovable))(vc)
  })
  private def removeUnusedLets(fd: FunDef): FunDef = inox.Bench.time("removing unused lets fd", {
    // println("removing unused lets from: " + fd.id.name)
    val res = transformFD((e: Expr) => removeUnusedLets(e))(fd)
    // println(fd)
    // println("------")
    // println(res)
    // println("------")
    // println("------")
    // println("------")
    // println("------")
    res
  })

  private def removeAssertsAndRequires(e: Expr): Expr = inox.Bench.time("removing asserts and requires", {
    exprOps.preMap({
      case a@Assert(_, _, body) => Some(body)
      case Require(pred, body) => Some(body)
      case _ => None
    }, applyRec=true)(e)
  })
  private val removeAssertsAndRequires: VC => VC = transformVC(removeAssertsAndRequires)
  private def removeAssertsAndRequires(funs: Map[Identifier, FunDef]): Map[Identifier, FunDef] = {
    funs.mapValues { fd =>
      val newBody = removeAssertsAndRequires(fd.fullBody)
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

    // println("VCs before simplification")
    // for (vc <- vcs) {
    //   println("AT " + vc.getPos)
    //   println(vc)
    //   println("======")
    // }

    val noassertFuns = removeAssertsAndRequires(syms.functions)
    val noassertVCs: Seq[VC] = vcs map removeAssertsAndRequires 

    def loop( funs: Map[Identifier, FunDef], 
              toVisit: Set[Identifier], 
              modifiers: Map[Identifier, List[Int]])
              : (Map[Identifier, FunDef], Map[Identifier, List[Int]]) = {
      if (toVisit.isEmpty) (funs, modifiers)
      else {

        val id = toVisit.head
        val fdTemp = funs(id)
        if (fdTemp.flags.exists(flag => flag match {
          case Extern => true
          case Unchecked => true
          case Annotation("library", _) => true
          case _ => false
        })) loop(funs, toVisit.tail, modifiers)
        else {
          val fd = removeUnusedLets(fdTemp)
          val funs2 = funs.updated(id, fd)
          val freeVariables = exprOps.variablesOf(fd.fullBody).map(v => v.id)
          fd.params.zipWithIndex.find { case (vd,_) => !freeVariables.contains(vd.id) } match {
            case Some((vd,i)) =>
              val calls = inox.Bench.time("getting callers", callers(fd).map(_.id))
              // println("Removing %s,%s of %s".format(vd.id.name, i, id.name))
              // println(fd)
              // println(fd.flags)
              // println("The callers are: %s".format(calls))

              val funs3 = calls.foldLeft(funs2) { case (funDefs, id2) =>
                val fd2 = funs2(id2)
                val newFD2 = removeParameter(fd2, id, i)
                funDefs.updated(fd2.id, newFD2)
              }
              val funs4 = funs3.updated(id, funs3(id).copy(
                params = removeIndex(funs3(id).params, i)
              ))
              val newModifiers = modifiers.updated(id, modifiers.getOrElse(id, Nil) :+ i)

              loop(funs4, toVisit.tail ++ calls, newModifiers)
            case None =>
              loop(funs2, toVisit.tail, modifiers)
         }
        }
      }
    }

    val (funs, modifiers) = loop(noassertFuns, noassertFuns.values.map(_.id).toSet, Map())
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