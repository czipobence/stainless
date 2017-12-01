package stainless
package verification

import CoqExpression._

trait CoqEncoder {
  implicit val debugSection = DebugSectionCoq

  val p: StainlessProgram
  val ctx: inox.Context
  val st: stainless.trees.type = stainless.trees

  import st._
  import p.symbols._
  import p.symbols.CallGraphOrderings._

  // ignore flags with an explicit warning
  def ignoreFlags(s: String, flags: Set[Flag]) = {
    if (!flags.isEmpty)
      ctx.reporter.warning(s"Coq translation ignored flags for $s:\n" + flags.mkString(", ") + "\n")
  }

  // transform a Stainless expression into a Coq expression
  def transformTree(t: st.Expr): CoqExpression = t match {
    case MatchExpr(scrut, cases) => 
      CoqMatch(transformTree(scrut), cases.map(makeFunctionCase))
    case Variable(id,tpe,flags) =>
      ignoreFlags(t.toString, flags)
      CoqVariable(id)
    case ADT(ADTType(id, targs), args) =>
      Constructor(CoqIdentifier(id), targs.map(transformType) ++ args.map(transformTree))
    case FunctionInvocation(id, targs, args) =>
      CoqApplication(CoqIdentifier(id), targs.map(transformType) ++ args.map(transformTree))
    case Application(t, ts) =>
      CoqApplication(transformTree(t), ts.map(transformTree))
    case FiniteSet(args,tpe) =>
      CoqFiniteSet(args map transformTree, transformType(tpe))
    case SetUnion(t1,t2) => CoqSetUnion(transformTree(t1), transformTree(t2))
    case ElementOfSet(t1,t2) => CoqBelongs(transformTree(t1), transformTree(t2))
    case Or(ts) => Orb(ts map transformTree)
    case And(ts) => Andb(ts map transformTree)
    case Implies(t1,t2) => implb(transformTree(t1), transformTree(t2))
    case Equals(t1,t2) => CoqEquals(transformTree(t1), transformTree(t2))
    case BooleanLiteral(true) => TrueBoolean
    case BooleanLiteral(false) => FalseBoolean
    case ADTSelector(adt, selector) => CoqSelector(transformTree(adt), CoqIdentifier(selector))
    case Forall(args, body) =>
      val params = args.map { case vd@ValDef(id,tpe,flags) => 
        ignoreFlags(vd.toString, flags)
        (CoqIdentifier(id), transformType(tpe)) 
      }
      CoqForall(params, CoqEquals(transformTree(body),TrueBoolean))
    case _ => ctx.reporter.fatalError(s"The translation to Coq does not support expression `${t.getClass}` yet.")
  }

  // creates a case for a match expression
  def makeFunctionCase(mc: MatchCase): CoqCase = mc match {
    case MatchCase(pattern, None, rhs) => 
      CoqCase(transformPattern(pattern), transformTree(rhs))
    case _ => ctx.reporter.fatalError(s"Guard in match cases are not supported by the Coq translation yet ($mc).")
  }

  // transform patterns that appear in match cases
  def transformPattern(p: Pattern): CoqPattern = p match {
    case ADTPattern(None, adtType, subPatterns) => 
      InductiveTypePattern(adtType.id, subPatterns.map(transformPattern))
    case WildcardPattern(None) => VariablePattern(None)
    case WildcardPattern(Some(ValDef(id,tpe,flags))) => 
      ignoreFlags(p.toString, flags)
      ctx.reporter.warning(s"Ignoring type $tpe in the wildcard pattern $p.")
      VariablePattern(Some(id))
    case _ => ctx.reporter.fatalError(s"Coq does not support patterns such as `$p` (${p.getClass}) yet.")
  }



  // transforms an ADT into an inductive type
  def transformADT(a: st.ADTDefinition): CoqCommand = {
    if (a.root(p.symbols) != a) {
      ctx.reporter.debug(s"Skipping $a, since it is not the root of the ADT.")
      NoCommand
    } else {
      a match {
        case a: st.ADTSort =>
          ignoreFlags(a.toString, a.flags)
          InductiveDefinition(
            a.id,
            a.tparams.map { case p => (p.id, TypeSort) },
            a.cons.map(id => makeCase(a.id, p.symbols.adts(id)))
          )
        case a: st.ADTConstructor =>
          ignoreFlags(a.toString, a.flags)
          InductiveDefinition(
            a.id,
            a.tparams.map { case p => (p.id, TypeSort) },
            Seq(makeCase(a.id, a))
          )
      }
    }
  }

  // creates a case for an inductive type
  def makeCase(root: Identifier, a: st.ADTDefinition) = a match { 
    case a: st.ADTConstructor =>
      ignoreFlags(a.toString, a.flags)
      val fieldsTypes = a.fields.map(vd => vd.tpe match {
        // FIXME: also check for recursive calls to other constructors
        case b: st.ADTType if a.id == b.id || root == b.id => // field using the type of `a` recursively
          CoqIdentifier(b.id)
        case _ => transformType(vd.tpe)
      })
      val arrowType = fieldsTypes.foldLeft[CoqExpression](CoqIdentifier(root))
        { case (acc,field) => Arrow(field,acc)}
      InductiveCase(a.id, arrowType)
    case _ =>
      ctx.reporter.fatalError(s"The translation to Coq does not support $a as a constructor.")
  }



  // transform function definitions
  def transformFunction(fd: st.FunDef): CoqCommand = {
    ignoreFlags(fd.toString, fd.flags)
    val mutual = p.symbols.functions.find{ case (_,fd2) => fd != fd2 && transitivelyCalls(fd, fd2) && transitivelyCalls(fd2, fd) }
    if (mutual.isDefined)
      ctx.reporter.fatalError(s"The translation to Coq does not support mutual recursion (between ${fd.id.name} and ${mutual.get._1.name}")
    else {
      val tparams: Seq[(Identifier,CoqExpression)] = fd.tparams.map { case p => (p.id, TypeSort) }
      val params: Seq[(Identifier,CoqExpression)] = fd.params.map { case vd => (vd.id, transformType(vd.tpe)) }
      val body = exprOps.withoutSpecs(fd.fullBody) match {
        case None => ctx.reporter.fatalError(s"We do not support functions with empty bodies: ${fd.id.name}")
        case Some(b) => transformTree(b)
      }
      val preconditionName = CoqEncoder.freshId()
      val preconditionParam: Seq[(Identifier,CoqExpression)] = exprOps.preconditionOf(fd.fullBody) match {
        case None => Seq()
        case Some(p) => Seq((preconditionName, transformTree(p)))
      }
      val returnType = exprOps.postconditionOf(fd.fullBody) match {
        case None => transformType(fd.returnType)
        case Some(Lambda(Seq(vd), post)) => 
          Refinement(CoqIdentifier(vd.id), transformType(vd.tpe), transformTree(post))
      }
      val allParams = tparams ++ params ++ preconditionParam
      if (fd.isRecursive) {
        FixpointDefinition(fd.id, allParams, returnType, body)
      } else {
        NormalDefinition(fd.id, allParams, returnType, body)
      }
    }
    // ctx.reporter.internalError("The translation to Coq does not support Functions yet.")
  }



  // translate a Stainless type to a Coq type
  def transformType(tpe: st.Type): CoqExpression = tpe match {
    case ADTType(id, args) if (adts(id).root == adts(id)) => 
      CoqApplication(CoqIdentifier(id), args map transformType)
    case TypeParameter(id,flags) => 
      ignoreFlags(tpe.toString, flags)
      CoqIdentifier(id)
    case BooleanType() => CoqBool
    case FunctionType(t1, t2) => 
      val tt1 = t1.map(transformType)
      tt1.foldLeft[CoqExpression](transformType(t2))
        { case (acc,arg) => Arrow(arg,acc) }
    case SetType(base) =>
      CoqSetType(transformType(base))
    case _ => ctx.reporter.fatalError(s"The translation to Coq does not support the type $tpe (${tpe.getClass}).")
  }

  def transform(): CoqCommand = {
    RequireImport("Coq.Program.Tactics") $
    RequireImport("Coq.Sets.Finite_sets") $
    p.symbols.adts.foldLeft[CoqCommand] (NoCommand) { case (acc,(_,adt)) => Sequence(acc,transformADT(adt)) } $
    p.symbols.functions.foldLeft[CoqCommand] (NoCommand) { case (acc,(_,fd)) => Sequence(acc,transformFunction(fd)) }
  }
}

object CoqEncoder {
  // to give unique names to the arguments we add for preconditions
  var i = 0
  val hypName = "stainlessPrecondition"

  def freshId(): Identifier = {
    i += 1 // we increment `i` atomically
    FreshIdentifier(hypName + "i")
  }

  def transformProgram(program: StainlessProgram, context: inox.Context) = {
    object encoder extends CoqEncoder {
      val p = program
      val ctx = context
    }

    encoder.transform()
  }
}