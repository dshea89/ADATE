datatype list = nil | cons of int * list
datatype option = none | some of list

type input_type = list * list
type output_type = option

%%

fun to_list [] = nil
  | to_list( X :: Xs ) = cons( Char.ord X, to_list Xs )

val Input_output_pairs = [
  ( ( "", "" ), SOME "" ),
  ( ( "", "abcd" ), NONE ),
  ( ( "a", "a" ), SOME "a" ),
  ( ( "a", "b" ), NONE ),
  ( ( "ab", "a" ), SOME "ab" ),
  ( ( "ab", "b" ), SOME "b" ),
  ( ( "ab", "c" ), NONE ),
  ( ( "ab", "ac" ), NONE ),
  ( ( "ab", "ab" ), SOME "ab" ),
  ( ( "ab", "abc" ), NONE ),
  ( ( "abc", "ac" ), NONE ),
  ( ( "abc", "ab" ), SOME "abc" ),
  ( ( "abc", "bc" ), SOME "bc" ),
  ( ( "abc", "c" ), SOME "c" ),
  ( ( "abcd", "" ), SOME "abcd" ),
  ( ( "abcd", "a" ), SOME "abcd" ),
  ( ( "abcd", "b" ), SOME "bcd" ),
  ( ( "abcd", "bc" ), SOME "bcd" ),
  ( ( "abbcd", "b" ), SOME "bbcd" ),
  ( ( "ababcd", "bc" ), SOME "bcd" ),
  ( ( "abcd", "ab" ), SOME "abcd" ),
  ( ( "abcd", "abc" ), SOME "abcd" ),
  ( ( "abcd", "abd" ), NONE ),
  ( ( "abcd", "abcd" ), SOME "abcd" ),
  ( ( "abcd", "abce" ), NONE ),
  ( ( "abcd", "abed" ), NONE ),
  ( ( "abcd", "c" ), SOME "cd" ),
  ( ( "abcd", "d" ), SOME "d" ),
  ( ( "abcd", "cd" ), SOME "cd" ),
  ( ( "abcd", "cde" ), NONE ),
  ( ( "abc", "defghi" ), NONE ),
  ( ( "abcbcdef", "bc" ), SOME "bcbcdef" ),
  ( ( "abcbcdef", "bcd" ), SOME "bcdef" ),
  ( ( "abcdefcdghijkdeflmnopdefrtaba", "defl" ), SOME "deflmnopdefrtaba" )
  ]

val Inputs = 
  map( fn( (X1,X2), _ ) => 
    ( to_list( String.explode X1 ), to_list( String.explode X2 ) ),
    Input_output_pairs )

val Outputs = 
  Array.fromList( 
    map( fn(_,Y) => 
      case Y of NONE => none | SOME Y => some( to_list( String.explode Y ) ),
      Input_output_pairs ) )

val Funs_to_use = 
  [ "false", "true", "=", "nil", "cons", "none", "some" ]

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

