datatype input = input of int * int * int * int * int
fun f ( ( X ) : input ) : int = raise D0
fun main ( ( X ) : input ) : int = f ( X )
%%
val Inputs = [ 148, 84, 52, 36, 28 ]
val Outputs = [ 24 ]
