datatype input = input of int * int * int * int * int
fun f ( ( X ) : input ) : int = raise D0
fun main ( ( X ) : input ) : int = f ( X )
%%
val Inputs = [ 9, 20, 6, 17, 3 ]
val Outputs = [ 14 ]
