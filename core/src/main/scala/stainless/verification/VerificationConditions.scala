/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.solvers.Solver
 
/** This is just to hold some history information. */
// nonRemovable: stores variable identifiers that are not to be simplified by the ProgramSimplifier
case class VC[T <: ast.Trees](condition: T#Expr, fd: Identifier, kind: VCKind, nonRemovable: Set[String] = Set()) extends inox.utils.Positioned {
  // def addNonRemovable(id: String) = VC(condition, fd, kind, nonRemovable + id)
  // def addNonRemovables(ids: Iterable[String]) = VC(condition, fd, kind, nonRemovable ++ ids)
}

sealed abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name
  def underlying = this
}

object VCKind {
  case class Info(k: VCKind, info: String) extends VCKind(k.abbrv+" ("+info+")", k.abbrv) {
    override def underlying = k.underlying
  }

  case object Precondition    extends VCKind("precondition", "precond.")
  case object LambdaPre       extends VCKind("lambda precondition", "lambda pre.")
  case object Postcondition   extends VCKind("postcondition", "postcond.")
  case object Assert          extends VCKind("body assertion", "assert.")
  case object ExhaustiveMatch extends VCKind("match exhaustiveness", "match.")
  case object ArrayUsage      extends VCKind("array usage", "arr. use")
  case object MapUsage        extends VCKind("map usage", "map use")
  case object Overflow        extends VCKind("integer overflow", "overflow")
  case object Shift           extends VCKind("strict arithmetic on shift", "shift")
  case object DivisionByZero  extends VCKind("division by zero", "div 0")
  case object ModuloByZero    extends VCKind("modulo by zero", "mod 0")
  case object RemainderByZero extends VCKind("remainder by zero", "rem 0")
  case object CastError       extends VCKind("cast correctness", "cast")
  case object PostTactic      extends VCKind("postcondition tactic", "tact.")
  case object Choose          extends VCKind("choose satisfiability", "choose")
  case object AdtInvariant    extends VCKind("adt invariant", "adt inv.")
  case class  AssertErr(err: String)  extends VCKind("body assertion: " + err, "assert.")
}

sealed abstract class VCStatus[+Model](val name: String) {
  override def toString = name
}

object VCStatus {
  case class Invalid[+Model](cex: Model) extends VCStatus[Model]("invalid")
  case object Valid extends VCStatus[Nothing]("valid")
  case object Unknown extends VCStatus[Nothing]("unknown")
  case object Timeout extends VCStatus[Nothing]("timeout")
  case object Cancelled extends VCStatus[Nothing]("cancelled")
  case object Crashed extends VCStatus[Nothing]("crashed")
  case object Unsupported extends VCStatus[Nothing]("unsupported")
}

case class VCResult[+Model](
  status: VCStatus[Model],
  solver: Option[Solver],
  time: Option[Long]
) {
  def isValid   = status == VCStatus.Valid
  def isInvalid = status.isInstanceOf[VCStatus.Invalid[_]]
  def isInconclusive = !isValid && !isInvalid
}

