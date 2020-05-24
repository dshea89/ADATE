(* File: ast_lib5.sml
   Created: 2000-03-23.
   Modified: 2000-03-23.
*)

structure Ast_lib5 :
sig

val real_pack : real -> string
val real_unpack : string -> real

val int_pack : int -> string
val int_unpack : string -> int
end =
struct

open Lib List1 C_interface

val Tmp_addr = Word32.toInt Tmp_addr

fun real_pack( X : real ) : string = (
  write_double( Tmp_addr, X );
  Byte.bytesToString( Word8Vector.tabulate( 8, fn I =>
    Word8.fromInt( peek( Tmp_addr+I ) ) ) ) )
  
exception Real_unpack_exn
fun real_unpack( S : string ) : real = 
  if String.size S <> 8 then raise Real_unpack_exn else (
  Word8Vector.appi ( fn( I, W ) => (poke( Tmp_addr+I, Word8.toInt W );()) )
    ( Byte.stringToBytes S, 0, NONE );
  read_double Tmp_addr )





exception Real_conversion_exn
fun test( to : real -> 'a, from : 'a -> real ) =
  for( 1, 10000, fn _ =>
  let
    val X = randReal() / randReal()
    val X = if randReal() < 0.5 then ~X else X
  in
    if real_rep_eq( X, from( to X ) ) then () else raise Real_conversion_exn
  end )

val () = test( real_pack, real_unpack )

exception Unexpected_Real_precision_exn

val () = 
  if Real.precision <> 52 then raise Unexpected_Real_precision_exn else ()


val int_pack = Int.toString
val int_unpack = fn S => case Int.fromString S of SOME N => N

end (* structure Ast_lib5 *)

