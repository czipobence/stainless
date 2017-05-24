import stainless.collection._
import stainless.lang._

trait T[UNUSED]  {
  def pure[A](x: A): List[A]
}

class C extends T[Int] {
  def pure[A](x: A): List[A] = List(x)

  def doublePure[A](x: A) = pure(x)
}
