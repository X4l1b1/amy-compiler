object WhileLoop {
	def fact(n: Int): Int = {
		var res: Int = 1;
		var j: Int = n;
		while(1 < j) {
			res = res * j;
			j = j - 1
		};
		res
	}
}

