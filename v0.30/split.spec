
datatype int_list = nil | cons of int * int_list
datatype pair_type = pair of int_list * int_list

type input_type = int_list
type output_type = pair_type

%%

fun from_list nil = []
  | from_list( cons(X1,Xs1) ) = X1 :: from_list Xs1

fun to_list [] = nil
  | to_list (X::Xs) = cons( X, to_list Xs )

val Inputs = [ 
  to_list [], 
  to_list [1], 
  to_list [1,2],
  to_list [1,2,3,4,5,6,7,8] ]

val Funs_to_use = [ "false", "true", "nil", "cons", "pair" ]

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

fun is_perm(Xs:int list,Ys) = Xs = sort (op<) Ys

fun output_eval_fun( _, Xs : input_type, pair(Ys,Zs) : output_type, _ )
  : output_eval_type * Grade.grade =
  let
    val Xs = from_list Xs
    val Ys = from_list Ys
    val Zs = from_list Zs
  in
    (
    if is_perm(Xs,Ys@Zs) andalso abs(length Ys - length Zs) <= 1 then
      correct
    else 
      wrong,
    ()
    )
  end

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
