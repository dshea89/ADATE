(* 
  File: lcs.sml
  Created: 1999-01-28
  Modified: 1999-01-28
*)

structure LCS :
  sig
    val llcs : ( 'a * 'a -> order ) * 'a list * 'a list -> int
  end =
struct
open Lib List1 

structure S = Splay_lib

exception LCS_exn1

fun llcs( cmp : 'a * 'a -> order, Xs : 'a list, Ys : 'a list ) : int =
let
  val Min_y_coords : ( int * int )Array.array =
    Array.array( length Xs + 1, ( Max_int, ~Max_int ) )

  fun get_y I = #2( Array.sub( Min_y_coords, I ) )

  fun bin_search( Lower : int, Upper : int, Y_new : int ) : int =
    if Y_new < get_y Lower then
      Lower
    else if Lower = Upper then
      raise LCS_exn1
    else if Lower + 1 = Upper then
      bin_search( Upper, Upper, Y_new )
    else
    let
      val Middle = ( Lower + Upper ) div 2
    in
      if Y_new < get_y Middle then
        bin_search( Lower, Middle, Y_new )
      else
        bin_search( Middle, Upper, Y_new )
    end (* fun bin_search *)

  val Last_used_index = ref 0

  fun update_min_y_coords( New as ( X, Y ) : int * int ) : unit = (
(*
    p( "\n(X,Y) = ( " ^ Int.toString X ^ ", " ^ Int.toString Y ^ " )\n" );
    p"\nMin_y_coords = ";
    loop( fn I => p(" " ^ Int.toString( get_y I ) ), 
      fromto( 1, !Last_used_index ) );
*)
    if !Last_used_index = 0 then (
      Array.update( Min_y_coords, 1, New );
      Last_used_index := 1 
      )
    else if Y = get_y( !Last_used_index ) then
      ()
    else if Y > get_y( !Last_used_index ) then (
      Array.update( Min_y_coords, !Last_used_index + 1, New );
      inc Last_used_index 
      )
    else
      Array.update( Min_y_coords, bin_search( 1, !Last_used_index, Y ), New )
  )

  val cmp = fn( ( Elem1, _ ), ( Elem2, _ ) ) => cmp( Elem1, Elem2 )

  fun build_splay( Ys : ( 'a * int )list ) : ( 'a * int list )SplayTree.splay =
  case Ys of
    nil => SplayTree.SplayNil
  | ( Y, I ) :: Ys =>
  case build_splay Ys of Ys =>
  case S.peek( cmp, ( Y, [] ), Ys ) of
    ( NONE, Ys ) => S.insert( cmp, ( Y, [ I ] ), Ys )
  | ( SOME( Elem, Indices ), Ys ) =>
  case S.delete( cmp, ( Y, [] ), Ys ) of Ys =>
    S.insert( cmp, ( Elem, I :: Indices ), Ys )

  val Ys_ref = ref( build_splay( rev( indexize( Ys, 1 ) ) ) ) 
in 
  loop( fn( X_elem, X ) => 
    loop( fn Y => update_min_y_coords( X, Y ), 
      case S.peek( cmp, ( X_elem, [] ), !Ys_ref ) of
        ( NONE, Ys ) => ( Ys_ref := Ys; [] )
      | ( SOME( _, Indices ), Ys ) => ( Ys_ref := Ys; Indices )
      ),
    indexize( Xs, 1 ) );

  !Last_used_index
end (* fun llcs *)

end (* structure LCS *)
  

