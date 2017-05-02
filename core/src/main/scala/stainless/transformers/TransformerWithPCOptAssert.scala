/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

trait TransformerWithPCOptAssert extends TransformerWithPC {

  val trees: ast.Trees
  import trees._
  import symbols._

  type Env = PathWithOptAsserts
  implicit val pp: PathProvider[Env] = new PathProvider[Env] {
    def empty = PathWithOptAsserts(Path.empty, Map())
  }

  case class PathWithOptAsserts(path: Path, optAsserts: Map[scala.Symbol, Expr]) extends PathLike[PathWithOptAsserts] {
    override def withBinding(p: (ValDef, Expr)) = PathWithOptAsserts(path withBinding p, optAsserts)

    override def withCond(expr: Expr) = {
//      println("with cond: " + expr)
      PathWithOptAsserts(path withCond expr, optAsserts)
    }

    def withConds(l: List[scala.Symbol]): PathWithOptAsserts = l match {
      case Nil => this
      case x :: xs =>
        if (optAsserts.contains(x))
          this.withCond(optAsserts(x)).withConds(xs)
        else
          sys.error("No assertion named '" + x + "' in that context.")
    }

    def withOptAssert(name: scala.Symbol, expr: Expr) = PathWithOptAsserts(path, optAsserts.updated(name, expr))

    override def merge(that: PathWithOptAsserts): PathWithOptAsserts = {
      val PathWithOptAsserts(path2, optAsserts2) = that
      PathWithOptAsserts(path merge path2, optAsserts ++ optAsserts2)
    }

    override def negate(): PathWithOptAsserts = {
      PathWithOptAsserts(path.negate, optAsserts)
    }

  }

  override protected def rec(e: Expr, env: PathWithOptAsserts): Expr = e match {

    case OptAssert(name, pred, err, body) =>
      val spred = rec(pred, env)
      val sbody = rec(body, env withOptAssert (name,spred))
      OptAssert(name, spred, err, sbody).copiedFrom(e)

    case ProofContext(assumptions, inside, body) =>
      val sinside = rec(inside, env withConds (assumptions))
      val sbody = rec(body, env)
      ProofContext(assumptions, sinside, sbody).copiedFrom(e)

    case _ => super.rec(e, env)
  }
}