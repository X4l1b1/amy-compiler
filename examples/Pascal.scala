object Pascal {

	// Computes the elements of Pascal's triangle given a column and row number
	def pascal(c: Int, r: Int): Int = {
		if(c == 0 || c==r){
			1
		}
		else {
			pascal(c, r - 1) + pascal(c - 1, r - 1)
		}
	}

	val s :String = "test";
	val s2 :String = "test";
	val s3: String = s;
	val i : Int = 0;
	val b :Boolean= true;
	val u :Unit= ();

	Std.printBoolean(s == "test");
	Std.printBoolean(s == s3);
	Std.printBoolean(s == s2);
	Std.printBoolean(u == ());
	Std.printBoolean(i == 2);
	Std.printBoolean(b == true);
	Std.printBoolean(b == false);
   

	Std.printString("Pascal(0, 2): " ++ Std.intToString(pascal(0, 2)));
	Std.printString("Pascal(1, 2): " ++ Std.intToString(pascal(1, 2)));
	Std.printString("Pascal(1, 3): " ++ Std.intToString(pascal(1, 3)))
}
