(*
  File: splay_lib.sml
  Taken out from lib.sml 1998-04-21
  Modified 1999-07-21
*)

signature SPLAY_LIB =
sig

val lub : 
  ( 'a * 'a -> order ) * 'a * 'a SplayTree.splay ->
  'a option * 'a SplayTree.splay

val glb : 
  ( 'a * 'a -> order ) * 'a * 'a SplayTree.splay ->
  'a option * 'a SplayTree.splay

(*
val find_all : 
  ( 'a * 'a -> order ) * 'a * 'a SplayTree.splay ->
  'a list * 'a SplayTree.splay
*)

val peek : 
  ( 'a * 'a -> order ) * 'a * 'a SplayTree.splay ->
  'a option * 'a SplayTree.splay

val min : 
  ( 'a * 'a -> order ) * 'a SplayTree.splay -> 'a * 'a SplayTree.splay

val insert : 
  ( 'a * 'a -> order ) * 'a * 'a SplayTree.splay -> 'a SplayTree.splay 

val delete : 
  ( 'a * 'a -> order ) * 'a * 'a SplayTree.splay -> 'a SplayTree.splay 

val delete_min : 
  ( 'a * 'a -> order ) * 'a SplayTree.splay -> 'a * 'a SplayTree.splay 

val inorder : 'a SplayTree.splay -> 'a list
val loop : ( 'a -> 'b ) * 'a SplayTree.splay -> unit
val map : ( 'a -> 'b ) * 'a SplayTree.splay -> 'b SplayTree.splay
val no_of_nodes : 'a SplayTree.splay -> int

val fromVector : 'a Vector.vector -> 'a SplayTree.splay
val fromList : 'a list -> 'a SplayTree.splay

val filter : ( 'a -> bool ) * 'a SplayTree.splay -> 'a SplayTree.splay

val splay_out :
  Lib.outstream * ( Lib.outstream * 'a -> unit ) * 'a SplayTree.splay ->
  unit

val is_ordered : ( 'a * 'a -> order ) * 'a SplayTree.splay -> bool

val splay_time : unit -> real

val copy : ('b*'b->order) * ('a->'b) * 'a SplayTree.splay -> 'b SplayTree.splay
end (* sig *)

structure Splay_lib : SPLAY_LIB =
struct

open Lib SplayTree LibBase

local

fun mk_spaces 0 = ""
  | mk_spaces N = " " ^ mk_spaces( N - 1 )

in

fun splay_out( out : outstream, node_out : outstream * 'a -> unit,
       Xs : 'a splay ) : unit =
  let
    fun g( N : int, Ys : 'a splay ) =
    case Ys of
      SplayNil => ( output( out, mk_spaces N ^ "SplayNil\n" ) )
    | SplayObj{ value, left, right } => (
        g( N+2, right );
        output( out, mk_spaces N );
        node_out( out,  value );
        output( out, "\n" );
        g( N+2, left )
        )
  in
    g( 0, Xs )
  end

end
    
      
fun no_of_nodes Xs =
  case Xs of
    SplayNil => 0
  | SplayObj{ value, left, right } => 
      1 + no_of_nodes left + no_of_nodes right

local

fun depth_sum( Depth, SplayNil ) = 0.0
  | depth_sum( Depth, SplayObj{ left, right, ... } ) =
      real Depth + depth_sum( Depth+1, left ) + depth_sum( Depth+1, right )

val Timer = mk_timer "Splay_lib"
  
in

exception Splay_tree_unbalanced_exn

fun balcheck( Xs, f ) =
let
(*
  val N = no_of_nodes Xs
  val N' = real(1+N)
  val () =
    if N < 100 then
      ()
    else if depth_sum( 0, Xs ) / N' > Math.ln N' * 8.0 then (
      splay_out( !std_out, fn( str, _ ) => p"*", Xs );
      raise Splay_tree_unbalanced_exn )
    else
      ()
*)
  val On = ref false
  val () = if timer_running Timer then On := true else start_timer Timer
  val Y = f()
  val () = if !On then () else stop_timer Timer
in
  Y
end

fun splay_time() = check_timer Timer

end (* local *)



fun is_ordered( cmp : 'a * 'a -> order, Xs : 'a splay ) : bool =
  case Xs of 
    SplayNil => true
  | SplayObj{ value = Ro, left, right } =>
  let
    val Ok_left =
      case left of
        SplayNil => true
      | SplayObj{ value, left, right } => 
      case cmp( value, Ro ) of
        GREATER => false
      | _ => true
      
    val Ok_right =
      case right of
        SplayNil => true
      | SplayObj{ value, left, right } => 
      case cmp( value, Ro ) of
        LESS => false
      | _ => true
  in
    Ok_left andalso Ok_right andalso
    is_ordered( cmp, left ) andalso is_ordered( cmp, right )
  end (* fun is_ordered *)
      
val is_ordered = fn(cmp,Xs) => balcheck( Xs, fn() => is_ordered(cmp,Xs) )

(* Prepare for SplayTree.splay: *)
fun cmpf cmp k k' = cmp(k', k)



local

fun lub'( cmp : 'a * 'a -> order, X : 'a, Xs : 'a splay ) : 'a option =
  case Xs of 
    SplayNil => NONE
  | SplayObj{ value, left, right } =>
  case cmp( X, value ) of
    LESS => (
      case lub'( cmp, X, left ) of
        NONE => SOME value
      | Y => Y
      )
  | EQUAL => SOME value
  | GREATER => lub'( cmp, X, right )

in

fun lub( cmp, X, Xs ) : 'a option * 'a splay =
  let
    val Xs = #2( splay( cmpf cmp X, Xs ) )
    val Y_opt = lub'( cmp, X, Xs )
  in
    ( Y_opt, Xs )
  end

val lub = fn(cmp,X,Xs) => balcheck( Xs, fn() => lub(cmp,X,Xs) )

end (* local *)


local

fun glb'( cmp : 'a * 'a -> order, X : 'a, Xs : 'a splay ) : 'a option =
  case Xs of 
    SplayNil => NONE
  | SplayObj{ value, left, right } =>
  case cmp( X, value ) of
    LESS => glb'( cmp, X, left )
  | EQUAL => SOME value
  | GREATER => (
      case glb'( cmp, X, right ) of
        NONE => SOME value
      | Y => Y
      )

in

fun glb( cmp, X, Xs ) : 'a option * 'a splay =
  let
    val Xs = #2( splay( cmpf cmp X, Xs ) )
    val Y_opt = glb'( cmp, X, Xs )
  in
    ( Y_opt, Xs )
  end

val glb = fn(cmp,X,Xs) => balcheck( Xs, fn() => glb(cmp,X,Xs) )
end (* local *)

(*

This code is commented out due to doubts about how the splaying affects
trees with duplicates.

local


fun grab( cmp : 'a * 'a -> order, X : 'a, Xs : 'a splay ) : 'a list =
  case Xs of
    SplayNil => []
  | SplayObj{ value, left, right } =>
  case cmp( X, value ) of
    LESS => []
  | GREATER => []
  | EQUAL => grab( cmp, X, left ) @ value :: grab( cmp, X, right )


fun fa( cmp : 'a * 'a -> order, X : 'a, Xs : 'a splay ) : 'a list =
  case Xs of
    SplayNil => []
  | SplayObj{ value, left, right } =>
  case cmp( X, value ) of
    LESS => fa( cmp, X, left )
  | GREATER => fa( cmp, X, right )
  | EQUAL => grab( cmp, X, Xs )

in

fun find_all( cmp, X, Xs ) : 'a list * 'a splay =
  let
    val Ys = fa( cmp, X, Xs )
  in
    ( Ys, #2( splay( fn V => cmp( V, X ), Xs ) ) )
  end

end

*)



fun peek( cmp, X, Xs ) : 'a option * 'a splay =
  case glb( cmp, X, Xs ) of ( Y, Xs ) =>
  case Y of
    NONE => ( Y, Xs )
  | SOME Y =>
  case cmp( X, Y ) of
    EQUAL => ( SOME Y, Xs )
  | _ => ( NONE, Xs )


val peek = fn(cmp,X,Xs) => balcheck( Xs, fn() => peek(cmp,X,Xs) )


local

fun min'( SplayObj{ value, left, ... } : 'a splay ) : 'a =
  case left of
    SplayNil => value
  | _ => min' left

in

fun min( cmp, Xs ) : 'a * 'a splay =
  let
    val Y = min' Xs
  in
    ( Y, #2( splay( cmpf cmp Y, Xs ) ) )
  end

val min = fn(cmp,Xs) => balcheck( Xs, fn() => min(cmp,Xs) )
end (* local *)



fun insert( cmp, X, SplayNil ) = 
      SplayObj{ value=X, left=SplayNil, right=SplayNil }
  | insert ( cmp, X, Xs ) =
  case splay( cmpf cmp X, Xs ) of
    ( EQUAL, SplayObj{ value, left, right } ) => 
        SplayObj{ value=X, left=left, right=right }

  | ( LESS, SplayObj{ value, left, right } ) => 
        SplayObj{ value = X, 
                  left = SplayObj{ value=value, left=left, right=SplayNil }, 
                  right = right }

  | ( GREATER, SplayObj{ value, left, right } ) => 
        SplayObj{ value = X,
                  left = left,
                  right = SplayObj{ value=value, left=SplayNil, right=right } }

val insert = fn(cmp,X,Xs) => balcheck( Xs, fn() => insert(cmp,X,Xs) )


fun splay_nil SplayNil = true
  | splay_nil _ = false

fun delete( cmp, X, Xs as SplayObj{...} ) =
  case splay( cmpf cmp X, Xs ) of
    ( EQUAL, SplayObj{ left, right, ... } ) =>
      if splay_nil left andalso splay_nil right then
        SplayNil
      else
        join( left, right )

val delete = fn(cmp,X,Xs) => balcheck( Xs, fn() => delete(cmp,X,Xs) )
  handle Ex => raise Ex

        
fun delete_min( cmp, Xs ) = (
  case min( cmp, Xs ) of ( X, Xs ) => ( X, delete( cmp, X, Xs ) )
  )
handle Ex => raise Ex

fun inorder SplayNil = []
  | inorder( SplayObj{ value, left, right } ) =
      inorder left @ value :: inorder right

fun loop( f, Xs ) =
  case Xs of
    SplayNil => ()
  | SplayObj{ value, left, right } => (
      loop( f, left );
      f value;
      loop( f, right )
      )
fun map( f, Xs ) =
  case Xs of
    SplayNil => SplayNil
  | SplayObj{ value, left, right } => 
      SplayObj{ 
        value = f value, 
        left = map( f, left ), 
        right = map( f, right ) }


local

fun f( Xs, First, Last ) =
  if First > Last then
    SplayNil
  else
    let
      val Middle = ( First + Last ) div 2
    in
      SplayObj{ value = Vector.sub( Xs, Middle ),
        left = f( Xs, First, Middle - 1 ),
        right = f( Xs, Middle + 1, Last ) }
    end

in (* local *)

fun fromVector( Xs : 'a Vector.vector ) : 'a splay =
  f( Xs, 0, Vector.length Xs - 1 )

end (* local *)

fun fromList( Xs : 'a list ) : 'a splay =
  fromVector( Vector.fromList Xs )
  
fun filter( p : 'a -> bool, Xs : 'a splay ) : 'a splay =
  fromList( List1.filter( p, inorder Xs ) )
  
fun copy( cmp : 'b*'b->order, convert : 'a->'b, Xs : 'a splay )  : 'b splay =
  fromList( cmpsort( cmp, List1.map( convert, inorder Xs ) ) )


end (* structure Splay_lib *)
