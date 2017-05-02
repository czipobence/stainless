/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait DefaultTactic extends Tactic {
  val description = "Default verification condition generation approach"

  import program._
  import program.trees._
  import program.symbols._

  def generatePostconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)
    (fd.postcondition, fd.body) match {
      case (Some(post), Some(body)) =>
        val vc = implies(fd.precOrTrue, application(post, Seq(body)))
        Seq(VC(vc, id, VCKind.Postcondition).setPos(post))
      case _ =>
        Nil
    }
  }

  def generatePreconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)

    val calls = transformers.CollectorWithPC(program) {
      case (fi: FunctionInvocation, path) if fi.tfd.precondition.isDefined => (fi, path)
    }.collect(fd.fullBody)

    calls.map { case (fi @ FunctionInvocation(_, _, args), path) =>
      val pre = fi.tfd.withParamSubst(args, fi.tfd.precondition.get)
      val vc = path implies pre
      val fiS = sizeLimit(fi.asString, 40)
      VC(vc, id, VCKind.Info(VCKind.Precondition, s"call $fiS")).setPos(fi)
    }
  }

  def generateCorrectnessConditions(id: Identifier): Seq[VC] = {

    def eToVCKind(e: Expr) = e match {
      case _ : MatchExpr =>
        VCKind.ExhaustiveMatch

      case BigAssert(_, _, _, _, _) =>
        VCKind.BigAssert

      case Assert(_, Some(err), _) =>
        if (err.startsWith("Array ")) {
          VCKind.ArrayUsage
        } else if (err.startsWith("Map ")) {
          VCKind.MapUsage
        } else if (err.startsWith("Division ")) {
          VCKind.DivisionByZero
        } else if (err.startsWith("Modulo ")) {
          VCKind.ModuloByZero
        } else if (err.startsWith("Remainder ")) {
          VCKind.RemainderByZero
        } else if (err.startsWith("Cast ")) {
          VCKind.CastError
        } else {
          VCKind.Assert
        }

      case _: Choose =>
        VCKind.Choose

      case _: Application =>
        VCKind.LambdaPre

      case _ =>
        VCKind.Assert
    }


    // We don't collect preconditions here, because these are handled by generatePreconditions
    val x = new transformers.CollectorWithPCOptAssert {

      type Result = (Expr, Expr)
      val trees: program.trees.type = program.trees
      val symbols: program.symbols.type = program.symbols

      def initEnv = PathWithOptAsserts(Path.empty, Map())

      //      private val fLifted = f.lift

      val f: PartialFunction[(Expr,PathWithOptAsserts), (Expr, Expr)] =  {
        case (m@MatchExpr(scrut, cases), env) =>
          (m, env.path implies orJoin(cases map (matchCaseCondition[Path](scrut, _).toClause)))

        case (e@Error(_, _), env) =>
          (e, Not(env.path.toClause))

        case (a@Assert(cond, _, _), env) =>
          (a, env.path implies cond)

        case (a@BigAssert(cond, _, _, _, props), env) =>
          (a, (env withConds(props)).path implies cond)

        case (app@Application(caller, args), env) =>
          (app, env.path implies Application(Pre(caller), args))

        case (c@Choose(res, pred), env) if !(res.flags contains Unchecked) =>
          (c, env.path implies Not(Forall(Seq(res), Not(pred))))
      }
      protected def step(e: Expr, env: PathWithOptAsserts): List[Result] = f.lift((e,env)).toList

    }

    val calls = x.collect2(getFunction(id).fullBody)
    calls.map { case (e, correctnessCond) =>
      VC(correctnessCond, id, eToVCKind(e)).setPos(e)
    }
  }
}

object DefaultTactic {
  def apply(p: StainlessProgram): DefaultTactic { val program: p.type } = new DefaultTactic {
    val program: p.type = p
  }
}
