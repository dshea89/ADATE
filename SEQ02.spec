datatype input = input of int * int * int * int * int * int * int
fun f ( ( X ) : input ) : int = raise D0
fun main ( ( X ) : input ) : int = f ( X )
%%
val Inputs = [ 2, 3, 5, 6, 7, 8, 10 ]
val Outputs = [ 11 ]
