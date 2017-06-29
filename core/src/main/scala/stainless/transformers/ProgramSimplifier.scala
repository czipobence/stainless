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

  private def removeParameter(vc: VC, id: Identifier, parameterToRemove: Int): VC = {
    verification.VC(removeParameter(vc.condition, id, parameterToRemove), vc.fd, vc.kind)
  }

  private def removeParameters(vc: VC, parametersToRemove: Map[Identifier, List[Int]]): VC = {
    verification.VC(removeParameters(vc.condition, parametersToRemove), vc.fd, vc.kind)
  }

  private def removeParameter(fd: FunDef, id: Identifier, parameterToRemove: Int): FunDef = {
    fd.copy(fullBody = removeParameter(fd.fullBody, id, parameterToRemove))
  }

  def transform(syms: Symbols, vcs: Seq[VC]): (Symbols, Seq[VC]) = {

    println("simplifying program")
//    println(syms)

    val noassertFuns = removeAssertsAndRequires(syms.functions)
    val noassertVCs = vcs.map(transformVC(removeAsserts))

    println("======================")
    println("removed asserts")
//    println(noassertSymbs)

    def loop( funs: Map[Identifier, FunDef], 
              toVisit: Set[Identifier], 
              modifiers: Map[Identifier, List[Int]])
              : (Map[Identifier, FunDef], Map[Identifier, List[Int]]) = {
      println("to visit: " + toVisit.size)
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
              // println(fd.flags)
              println("Removing %s at index %s from %s".format(vd,i,id.name))
              // println("The callers are")
              // println(calls.map(id => id.name))
              // println(fd)


              // inox.Bench.reportS()
              val funs2 = calls.foldLeft(funs) { case (funDefs, id2) =>
                val fd2 = funs(id2)
                // println("removing parameter (%s,%s) from: %s".format(id.name,i,fd2.id.name))
                val newFD2 = removeUnusedLets(removeParameter(fd2, id, i))
                // println(newFD2)
                funDefs.updated(fd2.id, newFD2)
              }
              val funs3 = funs2.updated(id, funs2(id).copy(
                params = removeIndex(funs2(id).params, i)
              ))
              val newModifiers = modifiers.updated(id, modifiers.getOrElse(id, Nil) :+ i)
              
              // println("new type!")
              val newFD = funs3(id)
              val tempSymbols = NoSymbols.withFunctions(funs3.values.toSeq).withADTs(syms.adts.values.toSeq)
              // println("===================")
              // println("===================")
              // println("===================")
              // println("===================")
              // println(tempSymbols)
              // println("===================")
              // println("===================")
              // println("===================")
              // println("===================")
              for (fdTemp <- funs3.values) {
                try {
                  tempSymbols.typeCheck(fdTemp.fullBody, fdTemp.returnType)
                } catch {
                  case e: Throwable =>
                    println("EXPLAINING: " + fdTemp.id.name)
                    println(tempSymbols.explainTyping(fdTemp.fullBody))
                    throw new Exception("YABLOL")
                }
                
                // try {
                //   tempSymbols.typeCheck(fdTemp.fullBody, fdTemp.returnType)
                // } catch {
                //   case e: Throwable => 
                //     tempSymbols.explainTyping(fdTemp.fullBody)
                // }
              }

              loop(funs3, toVisit.tail ++ calls, newModifiers)
            case None =>
              loop(funs, toVisit.tail, modifiers)
         }
        }
      }
    }

    val (funs, modifiers) = loop(noassertFuns, syms.functions.values.map(_.id).toSet, Map())
    // val (funs, modifiers) = (noassertFuns, Map[Identifier,List[Int]]())
    val newSyms = NoSymbols.withFunctions(funs.values.toSeq).withADTs(syms.adts.values.toSeq)
    
    // for (vc <- noassertVCs) {
    //   val newVC = removeUnusedLets(removeParameters(vc, modifiers))

    //   println("typechecking")
    //   println(newVC.condition)

    //   // println(newSyms.typeCheck(newVC.condition))
    // }
    
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