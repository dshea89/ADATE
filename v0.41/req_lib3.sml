(* 
  File: req_lib3.sml
  Created: 1998-08-19
  Modified: 1998-08-19
*)
  

functor Ladder( Ladder_arg :
    sig
      type req_node
      val Max_ladder_card : int
    end 
    ) :
  sig

type ladder

val empty_ladder : unit -> ladder

val insert :
  ( Ladder_arg.req_node * Ladder_arg.req_node -> order ) *
(* Smaller value is considered to be worse. *)
  ( { lower1 : Ladder_arg.req_node, upper1 : Ladder_arg.req_node,
      lower2 : Ladder_arg.req_node, upper2 : Ladder_arg.req_node 
    } ->
    order ) *
  Ladder_arg.req_node *
  ladder
  ->
  unit

type interval = Ladder_arg.req_node * Ladder_arg.req_node * int ref

val get_intervals : ladder -> interval SplayTree.splay 

val dummy_ladder : interval SplayTree.splay -> ladder

val ladder_cardinality : ladder -> int

type req_node_and_hits = Ladder_arg.req_node ref * int ref

val probabilistic_update : 'a * ( 'a ref * int ref ) -> unit

  end =
struct

open SplayTree Lib List1 Ast Ast_lib Print Ladder_arg

type interval = Ladder_arg.req_node * Ladder_arg.req_node * int ref

type req_node_and_hits = req_node ref * int ref
(* The int ref is used to probabilistically determine if the req_node is
   to be replaced by a new one that is equal according to pe_cmp but that
   might occur in a different position. This probabilistic sampling is employed
   to estimate losses due to prefix constraints during normalization.
*)

exception Probabilistic_update_exn
fun probabilistic_update( New : 'a, ( Old : 'a ref, Hits : int ref ) ) : unit =
  if !Hits <= 0 then
    raise Probabilistic_update_exn
  else (
    inc Hits; 
    if randReal() < 1.0 / real( !Hits ) then
      Old := New
    else
    ()
    )
    

type interval_node = req_node_and_hits * req_node_and_hits * int ref
(* ( Lower, Upper, No of eval values in interval so far ) *)

type diff_node = {
  lower1 : req_node, upper1 : req_node,
  lower2 : req_node, upper2 : req_node
  }

type ladder = interval_node splay ref * diff_node splay ref * int ref
(* ( Intervals, Heap organized according to U2-L1 differences, Cardinality ) *)

fun empty_ladder() : ladder =
  ( ref SplayNil, ref SplayNil, ref 0 )

structure S = Splay_lib

fun get_intervals( ( Intervals_ref, _, _  ) : ladder ) = 
  S.map( fn( ( Lower_ref, _ ), ( Upper_ref, _ ), N_ref ) =>
               ( !Lower_ref, !Upper_ref, N_ref ),
      !Intervals_ref )

fun dummy_ladder( Intervals : interval splay ) : ladder =
( ref( S.map( fn( Lower, Upper, N_ref ) =>
          ( (ref Lower, ref ~40), (ref Upper, ref ~50), N_ref ),
          Intervals ) ),
  ref SplayNil,
  ref( S.no_of_nodes Intervals ) )


fun ladder_cardinality( ( _, _, Card_ref ) : ladder ) : int = !Card_ref


fun member( pe_cmp, E, Glb_opt ) =
  case Glb_opt of
    NONE => false
  | SOME( ( L, _ ), ( U, _ ), N_ref ) =>
  case pe_cmp( E, !U ) of
    GREATER => false
  | _ => true

fun insert( pe_cmp, pe_diff_cmp, E : req_node,
      ( Intervals_ref, Diffs_ref, Card_ref ) : ladder ) : unit =
let
  fun interval_cmp( ( ( Lower, _ ), _, _ ), ( ( Lower', _  ), _, _ ) ) = 
    pe_cmp( !Lower, !Lower' )

  fun leq( X, Y ) = pe_cmp(X,Y) <> GREATER

  exception Pe_diff_cmp_exn
  fun pe_diff_cmp'( X as { lower1, upper1, lower2, upper2 } ) = (
    (
    if randReal() < 0.1 then
      if leq( lower1, upper1 )  andalso leq( lower2, upper2 ) then
        ()
      else
        raise Pe_diff_cmp_exn
    else
      () );
    pe_diff_cmp X )
  
  fun diff_cmp( { lower1, upper2, ... } : diff_node,
        { lower1 = lower1', upper2 = upper2', ... } : diff_node ) : order =
    case pe_diff_cmp'{ lower1 = lower1, upper1 = upper2, 
                      lower2 = lower1', upper2 = upper2' } of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL => pe_cmp( lower1, lower1' )

  val New = ( ( ref E, ref 1 ), ( ref E, ref 1 ), ref 1 )
  val ( Glb_opt, Intervals ) =
    S.glb( interval_cmp, New, !Intervals_ref )

  val () = 
    case Glb_opt of
      NONE => ()
    | SOME( ( Lower, Lower_hits ), ( Upper, Upper_hits ), N_ref ) => (
        ( case pe_cmp( E, !Lower ) of 
            EQUAL => probabilistic_update( E, ( Lower, Lower_hits ) )
          | _ => () );
        ( case pe_cmp( E, !Upper ) of 
            EQUAL => probabilistic_update( E, ( Upper, Upper_hits ) )
          | _ => () ) )

in
  if member( pe_cmp, E, Glb_opt ) then
    case Glb_opt of 
      SOME( _, _, N_ref ) => (
        inc N_ref;
        Intervals_ref := Intervals
        )
  else
let
  val ( Lub_opt, Intervals ) =
    S.lub( interval_cmp, New, Intervals )

  val Diffs = !Diffs_ref

  val Diffs =
    case Glb_opt of NONE => Diffs | SOME( ( L1, _ ), ( U1, _ ), _ ) =>
    case Lub_opt of NONE => Diffs | SOME( ( L2, _ ), ( U2, _ ), _ ) =>
      S.delete( diff_cmp,
        { lower1 = !L1, upper1 = !U1, lower2 = !L2, upper2 = !U2 },
        Diffs ) handle E => raise E

  val Diffs = 
    case Glb_opt of NONE => Diffs | SOME( ( L1, _ ), ( U1, _ ), _ ) =>
      S.insert( diff_cmp,
        { lower1 = !L1, upper1 = !U1, lower2 = E, upper2 = E },
        Diffs )
    
  val Diffs = 
    case Lub_opt of NONE => Diffs | SOME( ( L2, _ ), ( U2, _ ), _ ) =>
      S.insert( diff_cmp,
        { lower1 = E, upper1 = E, lower2 = !L2, upper2 = !U2 },
        Diffs )

  val Intervals = S.insert( interval_cmp, New, Intervals )

in
  if !Card_ref < Max_ladder_card then (
    inc Card_ref;
    Intervals_ref := Intervals;
    Diffs_ref := Diffs
    )
  else
let
  val ( { lower1, upper1, lower2, upper2 }, Diffs ) = 
    S.delete_min( diff_cmp, Diffs ) handle E => raise E

  fun mk( Lower, Upper ) = ( ( ref Lower, ref 0 ), ( ref Upper, ref 0 ), ref 0 )

  val ( SOME( Interval1 as ( ( L1, L1_hits ), ( U1, _ ), N1_ref ) ), 
        Intervals ) =
    S.peek( interval_cmp, mk( lower1, upper1 ), Intervals )

  val ( SOME( Interval2 as ( ( L2, _ ), ( U2, U2_hits ), N2_ref ) ), 
        Intervals ) =
    S.peek( interval_cmp, mk(lower2, upper2 ), Intervals )

  val Intervals = 
    S.delete( interval_cmp, Interval1, Intervals ) handle E => raise E

  val Intervals = 
    S.delete( interval_cmp, Interval2, Intervals ) handle E => raise E

  val ( Glb_opt, Intervals ) =
    S.glb( interval_cmp, Interval1, Intervals )

  val ( Lub_opt, Intervals ) =
    S.lub( interval_cmp, Interval1, Intervals )

  val Diffs = case Glb_opt of NONE => Diffs | SOME( ( L0, _ ), ( U0, _ ), _ ) =>
    S.delete( diff_cmp,
      { lower1 = !L0, upper1 = !U0, lower2 = !L1, upper2 = !U1 },
      Diffs ) handle E => raise E

  val Diffs = case Lub_opt of NONE => Diffs | SOME( ( L3, _ ), ( U3, _ ), _ ) =>
    S.delete( diff_cmp,
      { lower1 = !L2, upper1 = !U2, lower2 = !L3, upper2 = !U3 },
      Diffs ) handle E => raise E

  val Intervals = 
    S.insert( interval_cmp,
      ( ( L1, L1_hits ), ( U2, U2_hits ), ref( !N1_ref + !N2_ref ) ),
      Intervals )

  val Diffs = case Glb_opt of NONE => Diffs | SOME( ( L0, _ ), ( U0, _ ), _ ) =>
    S.insert( diff_cmp,
      { lower1 = !L0, upper1 = !U0, lower2 = !L1, upper2 = !U2 },
      Diffs )

  val Diffs = case Lub_opt of NONE => Diffs | SOME( ( L3, _ ), ( U3, _ ), _ ) =>
    S.insert( diff_cmp,
      { lower1 = !L1, upper1 = !U2, lower2 = !L3, upper2 = !U3 },
      Diffs )
in
  Intervals_ref := Intervals;
  Diffs_ref := Diffs
end
end
end (* fun insert *)

end (* functor Ladder *)
