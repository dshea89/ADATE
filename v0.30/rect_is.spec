
datatype point = point of int * int
datatype rect = rect of point * point
datatype option = none | some of rect

type input_type = rect * rect
type output_type = option

%%

fun to_rect( (X1,Y1), (X2,Y2) ) = rect( point(X1,Y1), point(X2,Y2) )
fun from_rect( rect( point(X1,Y1), point(X2,Y2) ) ) = ( (X1,Y1), (X2,Y2) )

val Input_output_pairs = 
[
( (((0,1000),(10,1020)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((0,1000),(10,1020))), NONE ),

( (((0,1030),(10,1050)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((0,1030),(10,1050))), NONE ),

( (((0,1060),(10,1080)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((0,1060),(10,1080))), NONE ),

( (((0,1090),(10,1110)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((0,1090),(10,1110))), NONE ),

( (((0,1120),(10,1140)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((0,1120),(10,1140))), NONE ),

( (((30,1000),(40,1020)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((30,1000),(40,1020))), NONE ),

( (((30,1030),(40,1050)), ((35,1045),(95,1095))), SOME((35,1045),(40,1050)) ),
( (((35,1045),(95,1095)), ((30,1030),(40,1050))), SOME((35,1045),(40,1050)) ),

( (((30,1060),(40,1080)), ((35,1045),(95,1095))), SOME((35,1060),(40,1080)) ),
( (((35,1045),(95,1095)), ((30,1060),(40,1080))), SOME((35,1060),(40,1080)) ),

( (((30,1090),(40,1110)), ((35,1045),(95,1095))), SOME((35,1090),(40,1095)) ),
( (((35,1045),(95,1095)), ((30,1090),(40,1110))), SOME((35,1090),(40,1095)) ),

( (((30,1120),(40,1140)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((30,1120),(40,1140))), NONE ),

( (((60,1000),(70,1020)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((60,1000),(70,1020))), NONE ),

( (((60,1030),(70,1050)), ((35,1045),(95,1095))), SOME((60,1045),(70,1050)) ),
( (((35,1045),(95,1095)), ((60,1030),(70,1050))), SOME((60,1045),(70,1050)) ),

( (((60,1060),(70,1080)), ((35,1045),(95,1095))), SOME((60,1060),(70,1080)) ),
( (((35,1045),(95,1095)), ((60,1060),(70,1080))), SOME((60,1060),(70,1080)) ),

( (((60,1090),(70,1110)), ((35,1045),(95,1095))), SOME((60,1090),(70,1095)) ),
( (((35,1045),(95,1095)), ((60,1090),(70,1110))), SOME((60,1090),(70,1095)) ),

( (((60,1120),(70,1140)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((60,1120),(70,1140))), NONE ),

( (((90,1000),(100,1020)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((90,1000),(100,1020))), NONE ),

( (((90,1030),(100,1050)), ((35,1045),(95,1095))), SOME((90,1045),(95,1050)) ),
( (((35,1045),(95,1095)), ((90,1030),(100,1050))), SOME((90,1045),(95,1050)) ),

( (((90,1060),(100,1080)), ((35,1045),(95,1095))), SOME((90,1060),(95,1080)) ),
( (((35,1045),(95,1095)), ((90,1060),(100,1080))), SOME((90,1060),(95,1080)) ),

( (((90,1090),(100,1110)), ((35,1045),(95,1095))), SOME((90,1090),(95,1095)) ),
( (((35,1045),(95,1095)), ((90,1090),(100,1110))), SOME((90,1090),(95,1095)) ),

( (((90,1120),(100,1140)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((90,1120),(100,1140))), NONE ),

( (((120,1000),(130,1020)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((120,1000),(130,1020))), NONE ),

( (((120,1030),(130,1050)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((120,1030),(130,1050))), NONE ),

( (((120,1060),(130,1080)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((120,1060),(130,1080))), NONE ),

( (((120,1090),(130,1110)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((120,1090),(130,1110))), NONE ),

( (((120,1120),(130,1140)), ((35,1045),(95,1095))), NONE ),
( (((35,1045),(95,1095)), ((120,1120),(130,1140))), NONE )
]

val Inputs = map( fn( (R1,R2), _ ) => ( to_rect R1, to_rect R2 ), 
  Input_output_pairs )

val Outputs = Array.fromList( 
  map( fn( _, NONE ) =>  none
       | ( _, SOME R3 ) => some( to_rect R3 ),
    Input_output_pairs ) )

val Funs_to_use = [ "<", "point", "rect", "none", "some" ]

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
