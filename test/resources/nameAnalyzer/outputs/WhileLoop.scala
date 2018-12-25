object WhileLoop_0 {
  def fact_0(n_0: Int): Int = {
    var res_0: Int =
      1;
    var j_0: Int =
      n_0;
    (While((1 < j_0)) {
      (
        res_0 =
          (res_0 * j_0);
        j_0 =
          (j_0 - 1)
      )
    });
    res_0
  }
}