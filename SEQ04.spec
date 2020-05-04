datatype input = input of int * int * int * int * int
fun f ( ( X ) : input ) : int = raise D0
fun main ( ( X ) : input ) : int = f ( X )
%%
val Inputs = [ 2, 3, 5, 9, 17 ]
val Outputs = [ 33 ]
