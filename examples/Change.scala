object Change {
	
	def count(money: Int, coins: L.List): Int = {
		coins match {
	        case L.Nil() => 0
	        case L.Cons(h, t) => 
	        	if (h <= 0){
	        		error("Negative coins not supported !")
	        	}
	        	else {
		        	if (money - h == 0){
		        		1
		        	}
		        	else {
		        		if (money - h < 0){
		        			0
		        		}
		        		else {
		        			countChange(money - h, coins) + countChange(money, t)
		        		}
		        	}
	        	}
	    }
	}

	// counts how many different ways you can make change for an amount, 
	// given a list of coin denominations. For example, there are 3 ways to give change 
	// for 4 if you have coins with denomiation 1 and 2: 1+1+1+1, 1+1+2, 2+2.
	def countChange(money: Int, coins: L.List): Int = {
      count(money, L.mergeSort(coins))
    }

	Std.printString("count(10, List(5, 4, 3, 2, 1)) = "  ++ Std.intToString(countChange(10, L.Cons(5, L.Cons(4, L.Cons(3, L.Cons(2, L.Cons(1, L.Nil()))))))));
	Std.printString("count(10, List(5, 2, 1)) = "  ++ Std.intToString(countChange(10, L.Cons(5, L.Cons(2, L.Cons(1, L.Nil()))))))
}