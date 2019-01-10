object Factorial_Imperative {
	def fact(i: Int) : Int = {
		var fact: Int = 1;// Declaration
		var index: Int = 2;
		while(index <= i){
			fact = fact*index;// Reassignment
			index = index + 1;
			Std.printString("current_fact = "  ++ Std.intToString(fact));
  			Std.printString("current_index = " ++ Std.intToString(index))
		};
		fact
	}
	Std.printString("5! = "  ++ Std.intToString(fact(5)));
  	Std.printString("10! = " ++ Std.intToString(fact(10)))
}