
object EmptyLoop {
  def foo = {
    val EOF = 0
    val x = 1
    while (x != EOF) { 
      val a = 3
      3 + a + 2
      a / 2
    } // forever
  }
}
