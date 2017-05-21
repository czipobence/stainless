/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait FunctionInlining extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: extraction.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._
    import symbols._
    import CallGraphOrderings._

    object transformer extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    }

    def levelOneInline(e: Expr) = {
      exprOps.postMap({
        case fi@FunctionInvocation(_, _, args) =>
          val tfd = fi.tfd
          if ((tfd.fd.flags contains Inline) && transitivelyCalls(tfd.fd, tfd.fd)) {
            throw MissformedStainlessCode(tfd.fd, "Can't inline recursive function: " + tfd.fd.id.name)
          }
          if (tfd.fd.flags contains Inline) {
            val (pre, body, post) = exprOps.breakDownSpecs(tfd.fullBody)
            body match {
              case None => throw MissformedStainlessCode(tfd.fd, "Inlining function with empty body: not supported")
              case Some(body) =>
                val newBody =
                  (pre, post) match {
                    case (None, None) => Dontcheck(body)
                    case (Some(pre), None) =>
                      Assert(pre, Some("Inlined precondition of " + tfd.fd.id.name), Dontcheck(body))
                    case (None, Some(lambda)) =>
                      val v = Variable.fresh("res", body.getType)
                      Let(v.toVal, Dontcheck(body), Assume(application(lambda, Seq(v)), v))
                    case (Some(pre), Some(lambda)) =>
                      val v = Variable.fresh("res", body.getType)
                      Assert(pre, Some("Inlined precondition of " + tfd.fd.id.name), Let(v.toVal, Dontcheck(body), Assume(application(lambda, Seq(v)), v)))
                  }
              Some(exprOps.freshenLocals((tfd.params zip args).foldRight(newBody: Expr) {
                 case ((vd, e), body) => let(vd, e, body)
              }))
            }
          } else {
            None
          }
        case _ => None
      }, applyRec = false)(e)
    }

    def deepInline(e: Expr) = {
      exprOps.preMap({
        case fi@FunctionInvocation(_, _, args) =>
          val tfd = fi.tfd
          if (tfd.fd.flags contains Inline) {
            val b1 = exprOps.freshenLocals((tfd.params zip args).foldRight(tfd.fullBody) {
              case ((vd, e), body) => let(vd, e, body)
            })
            exprOps.breakDownSpecs(b1)._2
          } else {
            None
          }
        case _ => None
      })(e)
    }

    t.NoSymbols
      .withADTs(symbols.adts.values.map(transformer.transform).toSeq)
      .withFunctions(symbols.functions.values.toSeq.sorted(functionOrdering).flatMap { fd =>
        if ((fd.flags contains Inline) && transitivelyCalls(fd, fd)) {
          throw MissformedStainlessCode(fd, "Can't inline recursive function")
        }

        if ((fd.flags contains Implicit) && (fd.flags contains Inline)) {
          None
        } else {
          Some(transformer.transform(fd.copy(
            fullBody = deepInline(levelOneInline(fd.fullBody)),
            flags = fd.flags - Inline
          )))
        }
      })
  }
}
