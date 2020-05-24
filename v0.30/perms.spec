
datatype int_list = nil | cons of int * int_list

datatype int_list_list = nil' | cons' of int_list * int_list_list

type input_type = int_list
type output_type = int_list_list

fun append( (Xs,Ys) : int_list * int_list ) : int_list =
  case Xs of
    nil => Ys
  | cons(X1,Xs1) => cons(X1,append(Xs1,Ys))

fun append'( (Xss,Yss) : int_list_list * int_list_list ) 
    : int_list_list =
  case Xss of
    nil' => Yss
  | cons'(Xs1,Xss1) => cons'(Xs1,append'(Xss1,Yss))



%%
fun from_list nil = []
  | from_list( cons(X1,Xs1) ) = X1 :: from_list Xs1

fun from_list' nil' = []
  | from_list'( cons'(Xs1,Xss1) ) =  from_list Xs1 :: from_list' Xss1

fun to_list [] = nil
  | to_list (X::Xs) = cons( X, to_list Xs )

val Inputs = 
      map( to_list, 
      map( fn N => fromto(1,N), fromto(0,4) ))

val Funs_to_use = [ "false", "true", "nil", "nil'", 
  "cons", "cons'", "append", "append'" ]

val NIL = string_to_symbol( func_sym, "nil" )
val NIL' = string_to_symbol( func_sym, "nil'" )
val APPEND = string_to_symbol( func_sym, "append" )
val APPEND' = string_to_symbol( func_sym, "append'" )
val CONS = string_to_symbol( func_sym, "cons" )
val CONS' = string_to_symbol( func_sym, "cons'" )

fun append_id_left( app_exp{ func, args=app_exp{func=F,...}::_, ...} ) = 
      func = APPEND andalso F = NIL
  | append_id_left _ = false

fun append_id_right( app_exp{ func, 
        args= _::app_exp{func=F,...}::_, ...} ) = 
      func = APPEND andalso F = NIL
  | append_id_right _ = false

fun append_assoc( app_exp{ func, 
        args= app_exp{ func=F, args=_::_::[], ...}::_, ...} ) = 
      func = APPEND andalso F = APPEND 
  | append_assoc _ = false

fun append_cons( app_exp{ func, args=app_exp{func=F,...}::_, ...} ) = 
      func = APPEND andalso F = CONS
  | append_cons _ = false


fun append_id_left'( app_exp{ func, args=app_exp{func=F,...}::_, ...} ) = 
      func = APPEND' andalso F = NIL'
  | append_id_left' _ = false

fun append_id_right'( app_exp{ func, 
        args= _::app_exp{func=F,...}::_, ...} ) = 
      func = APPEND' andalso F = NIL'
  | append_id_right' _ = false

fun append_assoc'( app_exp{ func, 
        args= app_exp{ func=F, args=_::_::[], ...}::_, ...} ) = 
      func = APPEND' andalso F = APPEND' 
  | append_assoc' _ = false

fun append_cons'( app_exp{ func, args=app_exp{func=F,...}::_, ...} ) = 
      func = APPEND' andalso F = CONS'
  | append_cons' _ = false

val Reject_funs = [
      append_id_left, append_id_right, append_assoc, append_cons,
      append_id_left', append_id_right', append_assoc', append_cons' ]

fun restore_transform D = D

structure Grade : GRADE =
struct

type grade = int
val zero = 0
val op+ = Int.+
val comparisons = [ Int.compare ]
val toString = Int.toString
val fromString = Int.fromString

end


fun make_set( Yss : int list list ) =
  fast_make_set( fn( Xs,Ys ) => list_less( op<, Xs, Ys ), Yss )

fun is_perm(Xs:int list,Ys) = Xs = sort (op<) Ys

fun output_eval_fun( _, Xs : input_type, Yss : output_type, _ )
  : output_eval_type * Grade.grade =
  let
    val Xs = from_list Xs
    val Yss = from_list' Yss
  in
    if exists( fn Ys => not(is_perm(Xs,Ys)), Yss ) then
      (wrong, 0)
    else
      case length(make_set Yss) of N => 
        if N = length Yss then
          (correct, ~N)
        else
          (wrong, 0)
  end


(* Uses 1.35s as upper limit for an scm class and 2s for a delta class.  *)

val N = 2
val Theta = 0.25
val Max_delta_class_card = N
val Delta_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 2.0, 1.0/real(N) )
val Max_output_class_card = N
val Max_scm_class_card = N
val Scm_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 1.35, 1.0/real(N) )

