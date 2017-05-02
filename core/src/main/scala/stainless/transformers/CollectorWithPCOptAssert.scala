/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

trait CollectorWithPCOptAssert extends TransformerWithPCOptAssert {
  import symbols._
  import trees._

  type Result

  private var results: List[Result] = Nil

  override type Env = PathWithOptAsserts
//  lazy val pp = implicitly[PathProvider[PathWithOptAsserts]]
  implicit val pp: PathProvider[PathWithOptAsserts]

  override protected def rec(e: Expr, current: Env): Expr = {
    accumulate(e, current)
    super.rec(e, current)
  }

  def transform2(e: Expr, init: Env): Expr = rec(e, init)
  def collect2(e: Expr) = {
    results = Nil
    transform2(e, PathWithOptAsserts(Path.empty,Map()))
    results
  }

  protected def step(e: Expr, env: PathWithOptAsserts): List[Result]

  protected def accumulate(e: Expr, env: Env): Unit = {
    results ++= step(e, env)
  }

}
