object Factorial {
  def fact(i: Int): Int = {
    if (i < 2) { 1 }
    else { 
      val rec: Int = fact(i-1);
      i * rec
    }
  }
  fact(5)
}
