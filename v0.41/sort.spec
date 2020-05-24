
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
  ( [7], [7] ),
  ( [5,6], [5,6] ),
  ( [1,0], [0,1] ),
  ( [0,1,2], [0,1,2] ),
  ( [0,2,1], [0,1,2] ),
  ( [1,0,2], [0,1,2] ),
  ( [1,2,0], [0,1,2] ),
  ( [2,0,1], [0,1,2] ),
  ( [2,1,0], [0,1,2] ) ] @
  flat_map( fn N => map( fn _ => ( scramble( fromto(1,N) ), fromto( 1, N ) ), 
                    fromto(1,4) ),
       fromto(4,10)  )  @
  [
  ( scramble( fromto( 1, 20 ) ), fromto( 1, 20 ) ),
  ( scramble( fromto( 1, 30 ) ), fromto( 1, 30 ) ),
  ( scramble( fromto( 1, 40 ) ), fromto( 1, 40 ) ),
  ( scramble( fromto( 1, 50 ) ), fromto( 1, 50 ) ),
  ( scramble( fromto( 1, 60 ) ), fromto( 1, 60 ) ),
  ( scramble( fromto( 1, 70 ) ), fromto( 1, 70 ) ),
  ( scramble( fromto( 1, 80 ) ), fromto( 1, 80 ) ),
  ( scramble( fromto( 1, 90 ) ), fromto( 1, 90 ) ),
  ( scramble( fromto( 1, 100 ) ), fromto( 1, 100 ) ),
  ( scramble( fromto( 1, 150 ) ), fromto( 1, 150 ) ),
  ( scramble( fromto( 1, 200 ) ), fromto( 1, 200 ) ),
  ( scramble( fromto( 1, 400 ) ), fromto( 1, 400 ) ),
  ( scramble( fromto( 1, 800 ) ), fromto( 1, 800 ) )
  ] 

val Validation_inouts = take( 10, Input_output_pairs ) @
  flat_map( fn N => map( fn _ => ( scramble( fromto(1,N) ), fromto( 1, N ) ), 
                    fromto(1,4) ),
       fromto(4,10)  ) @
  [
  ( scramble( fromto( 1, 100 ) ), fromto( 1, 100 ) ),
  ( scramble( fromto( 1, 200 ) ), fromto( 1, 200 ) ),
  ( scramble( fromto( 1, 400 ) ), fromto( 1, 400 ) ),
  ( scramble( fromto( 1, 800 ) ), fromto( 1, 800 ) )
  ]


val Inputs = map( to_list o #1, Input_output_pairs )
val Validation_inputs = map( to_list o #1, Validation_inouts )

val Outputs = Array.fromList( map( to_list o #2, 
  Input_output_pairs @ Validation_inouts ) )

val Abstract_types = []

val Funs_to_use = [ "false", "true", "<", "nil", "cons" ]

val Initial_program = NONE

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

val pack = fn _ => ""
val unpack = fn _ =>()

val post_process = fn _ => ()

val toRealOpt = NONE

end

fun output_eval_fun( I : int, _ : input_type, Y : output_type )
  : output_eval_type * Grade.grade =
  if Array.sub( Outputs, I ) <> Y then
    (wrong, ())
  else
    (correct, ())


(* Uses 1.35s as upper limit for an scm class and 2s for an LCS class.  *)

val N = 0
val Theta = 0.25
val Max_lcs_class_card = N
val LCS_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 2.0, 1.0/real(N) )
val Max_output_class_card = N
val Time_class_card = 0
val Max_scm_class_card = N
val Scm_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 1.35, 1.0/real(N) )


val Max_time_distribution = [ 
  10000, 
  50000, 
  250000 ]

val Pe_survival_weights = [ 0.05, 0.05, 0.1 ]
(* For pe3_cmp, pe2_cmp and pe1_cmp respectively. *)

