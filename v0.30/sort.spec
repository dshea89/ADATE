
datatype list = nil | cons of int * list

type input_type = list
type output_type = list

%%

fun to_list [] = nil
  | to_list( X :: Xs ) = cons( X, to_list Xs )

fun from_list nil = []
  | from_list( cons( X, Xs ) ) = X :: from_list Xs
  
val Input_output_pairs = [
  ( [], [] ),
  ( [0], [0] ),
  ( [0,1], [0,1] ),
  ( [1,0], [0,1] ),
  ( [0,1,2], [0,1,2] ),
  ( [0,2,1], [0,1,2] ),
  ( [1,0,2], [0,1,2] ),
  ( [1,2,0], [0,1,2] ),
  ( [2,0,1], [0,1,2] ),
  ( [2,1,0], [0,1,2] )
  ]

val Inputs = map( to_list o #1, Input_output_pairs )

val Outputs = Array.fromList( map( to_list o #2, Input_output_pairs ) )

val Funs_to_use = [ "false", "true", "<", "nil", "cons" ]

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

