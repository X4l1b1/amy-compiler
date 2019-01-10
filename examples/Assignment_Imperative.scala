object Assignment_Imperative {
	var i: Int;
	var j: Int = 0;
	i = j;
	j = i + 1;
	Std.printInt(i);
	Std.printInt(j) // prints 0, 1
}