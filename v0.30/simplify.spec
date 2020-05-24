datatype term_type = term of int * int

datatype pol = nil | cons of term_type * pol

type input_type = pol
type output_type = pol

%%
fun from_pol nil = []
  | from_pol( cons(term X1,Xs1) ) = X1 :: from_pol Xs1

fun to_pol [] = nil
  | to_pol (X::Xs) = cons( term X, to_pol Xs )

val Exponents = [
  [],
  [ 0 ],
  [ 0,0 ],
  [ 0,1 ],
  [ 0,0,0 ],
  [ 0,0,1 ],
  [ 0,1,0 ],
  [ 1,0,0 ],
  [ 0,1,2 ],
  [ 0,0,0,1 ],
  [ 0,0,1,2 ],
  [ 0,0,1,1 ],
  [ 0,1,0,1 ],
  [ 1,0,0,1 ],
  [ 0,1,0,2 ],
  [ 0,1,0,0 ],
  [ 0,0,0,1,1 ],
  [ 0,0,0,1,2 ],
  [ 0,0,1,0,1 ],
  [ 0,0,1,1,2 ],
  [ 0,2,1,1,0 ],
  [ 0,1,2,3,3 ],
  [ 0,1,2,0,0 ],
  [ 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,7,18,19,20,1,22,23,24,25,26,27,
    28,29 ]
  ]

val Inputs = 
  map( fn Xs => to_pol( combine( fromto( 101, 100 + length Xs), Xs ) ),
    Exponents )

val Funs_to_use = [ "+", "=", "false", "true","term", "nil", "cons" ]

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



fun real_eq(X:real,Y:real) = 
  if abs X < 1.0E~99 then
    abs Y < 1.0E~99
  else 
    not(abs Y < 1.0E~99) andalso not(abs X > 1.0E99) andalso 
    0.9999999 < X/Y andalso X/Y < 1.0000001

val Max_tmp = ln(1.0E99)

fun pow(X,Y) = 
  if X<=0.0 then 0.0 else
  let val Tmp = real Y * ln X
  in
    if Tmp > Max_tmp then 0.0 else exp Tmp
  end

fun eval_pol(Pol,X) =
  case Pol of
    [] => 0.0
  | (Coeff,Exponent)::Pol => 
  let val Tmp =  real Coeff*pow(X,Exponent) + eval_pol(Pol,X)
  in
    if Tmp > 1.0E99 orelse Tmp<0.0 then 0.0 else Tmp
  end


fun output_eval_fun( _, Xs : input_type, Ys : output_type, _ )
  : output_eval_type * Grade.grade =
  let 
    val X = 1.09431427443456197
    val Xs = from_pol Xs
    val Ys = from_pol Ys
    val N = length Ys 
  in
    if N = length( fast_make_set( fn( (_,E1), (_,E2) ) => E1 < E2, Ys ) ) 
       andalso real_eq( eval_pol(Xs,X), eval_pol(Ys,X) ) 
    then
      ( correct, () )
    else 
      ( wrong, () )
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

