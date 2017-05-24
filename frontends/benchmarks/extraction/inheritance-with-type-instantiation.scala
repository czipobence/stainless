trait Pure[A]  {
  def pure: A
}

class PureInt extends Pure[Int] {
  def pure = 0
}
