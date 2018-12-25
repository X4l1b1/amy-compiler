object WhileLoop {
  def fact(n: Int): Int = {
    var res: Int =
      1;
    var j: Int =
      n;
    (While((1 < j)) {
      (
        res =
          (res * j);
        j =
          (j - 1)
      )
    });
    res
  }
}
