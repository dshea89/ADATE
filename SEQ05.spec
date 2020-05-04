datatype input = input of int * int * int * int * int
fun f ( ( X ) : input ) : int = raise D0
fun main ( ( X ) : input ) : int = f ( X )
%%
val Inputs = [ 3, 7, 15, 31, 63 ]
val Outputs = [ 127 ]
