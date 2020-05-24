datatype bit = O | l

datatype unsigned = digit of bit | mku of unsigned * bit

type input_type = unsigned * unsigned
type output_type = unsigned

%%

fun int_to_unsigned 0 = digit O
  | int_to_unsigned 1 = digit l
  | int_to_unsigned N = mku( int_to_unsigned( N div 2 ), 
      case N mod 2 of 0 => O | 1 => l )

fun unsigned_to_int( digit O ) = 0
  | unsigned_to_int( digit l ) = 1
  | unsigned_to_int( mku( Xs, X ) ) = 2 * unsigned_to_int Xs +
      ( case X of O => 0 | l => 1 )

local

fun to [ #"0" ] = digit O
  | to [ #"1" ] = digit l
  | to( X :: Xs ) = case to [X] of digit X => mku( to Xs, X )

in

fun to_unsigned Xs = to( rev( explode Xs ) )

end

val Inputs = 
  let
    val N = 7
    val Xs = map( int_to_unsigned, fromto( 0, N ) )
    val Ys = map( int_to_unsigned, [100, 1000, 10000, 100000] )
  in
    cart_prod( Xs, Xs ) @ cart_prod( Ys, Ys )
  end

val Outputs = Array.fromList(
  map( fn( X1, X2 ) => 
    int_to_unsigned( unsigned_to_int X1 + unsigned_to_int X2 ),
    Inputs ) )

val Funs_to_use = [ "false", "true", "O", "l", "digit", "mku" ]

val Reject_funs = []
fun restore_transform D = D


structure Grade : GRADE =
struct

type grade = unit
val zero = ()
val op+ = fn(_,_) => ()
val comparisons = [ fn _ => EQUAL ]
val toString = fn _ => ""
val fromString = fn _ => SOME()

end

fun output_eval_fun( I : int, _ : input_type, Y : output_type, _ )
  : output_eval_type * Grade.grade =
  if Array.sub( Outputs, I ) <> Y then
    (wrong, ())
  else
    (correct, ())

(* Uses 1.35s as upper limit for an scm class and 2s for a delta class.  *)

val N = 0
val Theta = 0.25
val Max_delta_class_card = N
val Delta_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 2.0, 1.0/real(N) )
val Max_output_class_card = N
val Max_scm_class_card = N
val Scm_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 1.35, 1.0/real(N) )

