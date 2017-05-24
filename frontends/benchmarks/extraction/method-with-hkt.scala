import scala.language.higherKinds

trait Traverse {
  def traverse[G[_]] = 1
}
