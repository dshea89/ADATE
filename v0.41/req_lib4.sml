(*
  File: req_lib4.sml
  Created: 1998-08-19
  Modified: 1999-05-24
*)



functor Map( 
    Map_arg :
      sig
        val Version : string
        type eval_type
        val truncate_syntactic_complexities : eval_type -> eval_type
        val print_eval: eval_type -> unit
        val syntactic_fingerprint : eval_type -> real
        val Max_REQ_storage : int
        type REQ_record
        val Dummy_REQ_record : REQ_record
      end
    ) :
  sig
    type map_data
    type cum_map_data
    type req_node = Map_arg.eval_type * Map_arg.REQ_record
    type data0 (* From Random_ladder in req_lib6.sml. *)
    type data2
    val empty_map : bool (* true iff this is the first map. This map has higher
                            REQ_PQ cardinality *) *
      ( Map_arg.eval_type * Map_arg.eval_type -> order ) *
      ( { lower1 : Map_arg.eval_type, upper1 : Map_arg.eval_type,
          lower2 : Map_arg.eval_type, upper2 : Map_arg.eval_type 
         } -> 
        order )
      -> map_data
    val empty_data0 : unit -> data0
    val insert : req_node * map_data list * data0 -> unit
    type make_merged_cum_map_range
    val get_req_pq_prefix : make_merged_cum_map_range -> req_node list
    val get_other_reqs_and_mults 
        : make_merged_cum_map_range -> ( req_node * int ) list
    val make_merged_cum_map :
      ( real * map_data ) list * data0 -> make_merged_cum_map_range
    val  order_no : req_node * make_merged_cum_map_range -> int
    val map_time : unit -> real
  end
=
struct

open SplayTree Lib List1 Ast Ast_lib Print

type req_node = Map_arg.eval_type * Map_arg.REQ_record


val Map_timer = mk_timer "Map_timer"

fun map_time() = check_timer Map_timer

structure Ladder =
  Ladder(
    struct
      type req_node = req_node
      val Max_ladder_card = Map_arg.Max_REQ_storage
    end 
    )


type eval_pq_node = Ladder.req_node_and_hits

type map_data = {
  first : bool,

  no_of_insertions : int ref,

  pe_cmp : req_node * req_node -> order,

  req_pq_cmp : req_node * req_node -> order,

  eval_pq_cmp : eval_pq_node * eval_pq_node -> order,

  interval_cmp : Ladder.interval * Ladder.interval -> order,

  pe_diff_cmp :
    { lower1 : req_node, upper1 : req_node,
      lower2 : req_node, upper2 : req_node } ->
    order,
  
  req_pq : req_node splay ref * int ref,

  eval_pq : eval_pq_node splay ref * int ref,
  
  ladder : Ladder.ladder
  }

fun print_req_node( ( E, _ ) : req_node ) : unit =
  Map_arg.print_eval E

fun empty_map(  First : bool, pe_cmp, pe_diff_cmp ) : map_data = 
let
  fun req_pq_cmp( ( E1 : Map_arg.eval_type, _ ), 
                  ( E2 : Map_arg.eval_type, _ ) ) =
    case pe_cmp( E2, E1 ) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL => 
        real_compare( 
          Map_arg.syntactic_fingerprint E1, 
          Map_arg.syntactic_fingerprint E2 )
    

  fun eval_pq_cmp( ( Rn_ref1, _ ), ( Rn_ref2, _ ) ) =
    case !Rn_ref1 of ( E1, _ ) =>
    case !Rn_ref2 of ( E2, _ ) =>
    pe_cmp( Map_arg.truncate_syntactic_complexities E2,
            Map_arg.truncate_syntactic_complexities  E1 )

  val t = Map_arg.truncate_syntactic_complexities
    
  fun interval_cmp( ( ( Lower, _ ), _, _ ), ( ( Lower', _ ), _, _ ) ) = 
    (cmp_invert pe_cmp)( t Lower, t Lower' )

in {
  first = First,
  no_of_insertions = ref 0,
  pe_cmp = fn( ( E1, _ ), ( E2, _ ) ) => pe_cmp( E1, E2 ),
  req_pq_cmp = req_pq_cmp,
  eval_pq_cmp = eval_pq_cmp,
  interval_cmp = interval_cmp,
  pe_diff_cmp = 
    fn{ lower1 = ( l1, _ ), upper1 = ( u1, _ ), 
        lower2 = ( l2, _ ), upper2 = ( u2, _ ) } =>
      pe_diff_cmp{ lower1 = t u2, upper1 = t l2, lower2 = t u1, upper2 = t l1 },
  req_pq = ( ref SplayNil, ref 0 ),
  eval_pq = ( ref SplayNil, ref 0 ),
  ladder = Ladder.empty_ladder()
  }
end (* fun empty_map *)
  
structure S = Splay_lib

fun req_pq_member( New,
      { req_pq_cmp, req_pq = ( Xs_ref, _ ), ... } : map_data ) : bool =
  case S.peek( req_pq_cmp, New, !Xs_ref ) of
    ( SOME _, Xs ) => ( Xs_ref := Xs; true )
  | ( NONE, Xs ) => ( Xs_ref := Xs; false )

fun req_pq_insert( New,
      { first, req_pq_cmp, req_pq = ( Xs_ref, Card_ref ), ... } : map_data 
      ) : req_node option = 
let
  val Xs = S.insert( req_pq_cmp, New, !Xs_ref )
in
  if !Card_ref < (if first then 24 else 1 ) * Map_arg.Max_REQ_storage then (
    inc Card_ref;
    Xs_ref := Xs;
    NONE
    )
  else
  case S.delete_min( req_pq_cmp, Xs ) handle E => raise E of ( Worst, Xs ) => (
    Xs_ref := Xs;
    SOME Worst
    )
end (* fun req_pq_insert *)
    
fun eval_pq_insert( Rn : req_node, 
      { eval_pq_cmp, eval_pq = ( Xs_ref, Card_ref ), ... } : map_data
      ) : ( req_node * int ) option =
let
  val New = ( ref Rn, ref 1 )
in
  case S.peek( eval_pq_cmp, New, !Xs_ref ) of
    ( SOME( Rn_ref, N_ref ), Xs ) => ( 
        Ladder.probabilistic_update( Rn, ( Rn_ref, N_ref ) );
        Xs_ref := Xs; 
        NONE )
  | ( NONE, Xs ) =>
let
  val Xs = S.insert( eval_pq_cmp, New, Xs )
in
  if !Card_ref < Map_arg.Max_REQ_storage then (
    inc Card_ref;
    Xs_ref := Xs;
    NONE
    )
  else
  case S.delete_min( eval_pq_cmp, Xs ) handle E => raise E of 
    ( Worst as ( Rn_ref, N_ref ), Xs ) => (
        Xs_ref := Xs;
        SOME( !Rn_ref, !N_ref )
    )
end
end (* fun eval_pq_insert *)

local

fun insert1( New, 
      Map as { pe_diff_cmp, interval_cmp, ladder, no_of_insertions, ... } 
      : map_data ) 
    : unit = (
  inc no_of_insertions; (
  case req_pq_insert( New, Map ) of
    NONE => ()
  | SOME Rn =>
  case eval_pq_insert( Rn, Map ) of
    NONE => ()
  | SOME( Rn, N ) => 
      for( 1, N, fn _ => 
        Ladder.insert( 
          fn( X, Y ) => interval_cmp( ( X, X, ref 0 ), ( Y, Y, ref 0 ) ),
          pe_diff_cmp, 
          Rn, 
          ladder ) )
  ) )

in (* local *)

fun insert( New, Maps ) : unit = (
  start_timer Map_timer;
  if exists( fn Map => req_pq_member( New, Map ), Maps ) then 
    ()
(*
  let
    val { req_pq_cmp, req_pq = ( Xs_ref, N_ref ), ... } :: _ =
      filter( fn Map => req_pq_member( New, Map ), Maps )
    val ( SOME Old, Xs ) = S.peek( req_pq_cmp, New, !Xs_ref )
  in
    Xs_ref := Xs;
    p"\ninsert: Rejecting New =\n"; print_req_node New; nl();
    p"  Old =\n"; print_req_node Old; nl();nl();nl()
  end
*)
  else
    loop( fn Map => insert1( New, Map ), Maps );
  stop_timer Map_timer
  )

end (* local *)


(* The following function is only used for debugging. *)
(*
fun map_member( Rn : req_node,
      Map as { eval_pq_cmp, eval_pq = ( Xs_ref, Card_ref ), 
               interval_cmp, ... } : map_data,
      Intervals_ref : Ladder.interval splay ref
      ) : bool =
  req_pq_member( Rn, Map ) 
    orelse (
  case S.peek( eval_pq_cmp, ( ref Rn, ref 0 ), !Xs_ref ) of
    ( SOME _, Xs ) => ( Xs_ref := Xs; true )
  | ( NONE, Xs ) => ( Xs_ref := Xs; false ) ) 
    orelse 
    let
      val ( SOME( Lower, Upper, N_ref ), Intervals ) =
        S.glb( interval_cmp, ( Rn, Rn, ref 0 ), !Intervals_ref )
      val _ = Intervals_ref := Intervals
      fun cmp( Rn1, Rn2 ) = 
        interval_cmp( ( Rn1, Rn1, ref 0 ), ( Rn2, Rn2, ref 0 ) )
    in
      case cmp( Lower, Rn ) of
        GREATER => false 
      | _ => (* Lower <= Rn *)
      case cmp( Rn, Upper ) of
        GREATER => false
      | _ => true
    end
*)


type cum_req_node = int ref * req_node

type cum_eval_pq_node = int ref * int ref * eval_pq_node
(* ( Start order no, No of order no assignments so far, ... ) *)

type cum_interval = int ref * int ref * Ladder.interval


type cum_map_data = {
(* The first two fields below are only used for error checking. *)
  expected_no_of_hits : int,
  no_of_hits_so_far : int ref,

  overproduction_order_no : int ref,

  cum_req_pq_cmp : cum_req_node * cum_req_node -> order,

  cum_eval_pq_cmp : cum_eval_pq_node * cum_eval_pq_node -> order,

  cum_intervals_cmp : cum_interval * cum_interval -> order,

  cum_req_pq : cum_req_node splay ref,

  cum_eval_pq : cum_eval_pq_node splay ref,
  
  cum_intervals : cum_interval splay ref
  }


fun cum_req_pq_member( New,
      { cum_req_pq_cmp, cum_req_pq, ... } : cum_map_data ) : bool =
  case !cum_req_pq of Xs =>
  case S.peek( cum_req_pq_cmp, ( ref 0, New ), Xs) of
    ( SOME _, Xs ) => ( cum_req_pq := Xs; true )
  | ( NONE, Xs ) => ( cum_req_pq := Xs; false )

  
fun req_pq_to_cum_req_pq( cum_cmp, 
      { req_pq = ( Xs_ref, _ ), ...} : map_data ) =
    S.copy( cum_cmp, fn( X : req_node ) => ( ref 0, X ), !Xs_ref )

fun eval_pq_to_cum_eval_pq( cum_cmp,
      { eval_pq = ( Xs_ref, _ ), ... } : map_data ) =
  S.copy( cum_cmp, fn( X : eval_pq_node ) => ( ref 0, ref 0, X ), !Xs_ref )

fun ladder_to_cum_intervals( { ladder, ... } : map_data ) =
  S.map( fn( X : Ladder.interval ) => ( ref 0, ref 0, X ), 
    Ladder.get_intervals ladder )

exception Make_cum_map_data_exn
fun make_cum_map_data( Cumulate : bool,
      Map as { req_pq_cmp, eval_pq_cmp, interval_cmp, 
               no_of_insertions, ... } : map_data
    ) : cum_map_data =
let
  val cum_req_pq_cmp = 
    fn( ( _, X1 ), ( _, X2 ) ) => req_pq_cmp( X2, X1 )

  val cum_eval_pq_cmp = 
    fn( ( _, _, X1 ), ( _, _, X2 ) ) => eval_pq_cmp( X2, X1 )

  val Cum_req_pq = req_pq_to_cum_req_pq( cum_req_pq_cmp, Map )
  val Cum_eval_pq = eval_pq_to_cum_eval_pq( cum_eval_pq_cmp, Map )
  val Cum_intervals = ladder_to_cum_intervals Map
  val So_far_ref = ref 0
in
  if Cumulate then (
    S.loop( fn( Order_no_ref, _ ) => ( 
      inc So_far_ref; 
      Order_no_ref := !So_far_ref 
      ),
      Cum_req_pq );
  
    S.loop( fn( Start_ref, _, ( _, N_ref ) : eval_pq_node ) =>
      if !N_ref < 0 then raise Make_cum_map_data_exn else (
      Start_ref := !So_far_ref + 1;
      So_far_ref := !So_far_ref + !N_ref
      ),
      Cum_eval_pq );
  
    loop( fn( Start_ref, _, ( _, _, N_ref ) : Ladder.interval ) => 
      if !N_ref < 0 then raise Make_cum_map_data_exn else (
      Start_ref := !So_far_ref + 1;
      So_far_ref := !So_far_ref + !N_ref
      ),
      rev( S.inorder Cum_intervals ) )
    )
  else
    ();
  {
  expected_no_of_hits = !no_of_insertions,

  no_of_hits_so_far = ref 0,

  overproduction_order_no = ref 0,
  
  cum_req_pq_cmp = cum_req_pq_cmp,

  cum_eval_pq_cmp = cum_eval_pq_cmp,

  cum_intervals_cmp = fn( ( _, _, X1 ), ( _, _, X2 ) ) => 
    interval_cmp( X1, X2 ), 

  cum_req_pq = ref Cum_req_pq,

  cum_eval_pq = ref Cum_eval_pq,
  
  cum_intervals  = ref Cum_intervals
  }

end (* fun make_cum_map_data *)

  

datatype order_no_arg =
    start_at_req_pq of req_node
  | start_at_eval_pq of req_node
  | start_at_intervals of req_node

fun order_no_arg_req_node X =
  case X of
    start_at_req_pq Rn => Rn
  | start_at_eval_pq Rn => Rn
  | start_at_intervals Rn => Rn 

fun dummy_eval_pq_node( Rn : req_node ) : eval_pq_node =
  ( ref Rn, ref(~10) )

exception Overproduction_exn
fun order_no'( X : order_no_arg, No_ladder : bool,
      { expected_no_of_hits, no_of_hits_so_far, overproduction_order_no,
        cum_req_pq_cmp, cum_eval_pq_cmp, cum_intervals_cmp,
        cum_req_pq, cum_eval_pq, cum_intervals, ... } : cum_map_data   
      ) : int option = (
  inc no_of_hits_so_far;
  if !no_of_hits_so_far > ceil( 1.3 * real expected_no_of_hits ) + 10 then (
    output( !std_err, 
      "\n\nWARNING: req_lib4.sml: Version = " ^ Map_arg.Version ^ 
      "Unexpectedly many hits!\n" ^
      "no_of_hits_so_far = " ^ Int.toString( !no_of_hits_so_far ) ^
      "\nexpected_no_of_hits = " ^ Int.toString( expected_no_of_hits) ^ "\n" );
    flush_out( !std_err )
    )
  else
    ();
  case
    case X of
      start_at_req_pq X => (
        case S.peek( cum_req_pq_cmp, ( ref 0, X ), !cum_req_pq ) of
          ( SOME( Y as ( N_ref, _ ) ), Xs ) => 
              ( (* cum_req_pq := S.delete( cum_req_pq_cmp, Y, Xs ); *)
                SOME( !N_ref ) )
        | ( NONE, Xs ) => ( cum_req_pq := Xs; NONE )
        )
    | _ => NONE
  of
    SOME N => SOME N
  | NONE =>
  let
    val Rn_opt = 
      case X of
        start_at_req_pq Rn => SOME Rn
      | start_at_eval_pq Rn => SOME Rn
      | _ => NONE
  in
  case
    case Rn_opt of
      NONE => NONE
    | SOME Rn =>
    case S.peek( cum_eval_pq_cmp, ( ref 0, ref 0, dummy_eval_pq_node Rn ), 
           !cum_eval_pq ) 
    of
      ( SOME( Y as ( N_ref, Hits_ref, ( _, Count_ref ) ) ), Xs ) => ( 
          inc Hits_ref;
          cum_eval_pq := (
            if !Hits_ref = !Count_ref then
              Xs (* S.delete( cum_eval_pq_cmp, Y, Xs ) *)
            else
              Xs );
          SOME( !N_ref + !Hits_ref - 1 ) 
          )
    | ( NONE, Xs ) => ( cum_eval_pq := Xs; NONE )
  of
    SOME N => SOME N
  | NONE =>
  if No_ladder then NONE else
  let
    val Rn = order_no_arg_req_node X
    fun overproduction() = (
      (
      if !overproduction_order_no = 0 then
        overproduction_order_no := expected_no_of_hits - 1
      else
        () );
      inc overproduction_order_no;
      !overproduction_order_no )
  in
  case S.glb( cum_intervals_cmp, ( ref 0, ref 0, ( Rn, Rn, ref 0 ) ),
        !cum_intervals )
  of 
    ( SOME( N_ref, Hits_ref, _ ), Xs ) => ( 
        cum_intervals := Xs; 
        inc Hits_ref;
        SOME( !N_ref + !Hits_ref - 1 )
        )
  | ( NONE, Xs ) => ( cum_intervals := Xs; 
  (
  case Xs of
    SplayNil => SOME( overproduction() )
  | _ =>  SOME Max_int
  ) )
  end
  end (* fun order_no' *)
  )

fun order_no( X : order_no_arg, Cum_map ) : int =
  case order_no'( X, false, Cum_map ) of SOME N => N


fun merged_order_no( X : order_no_arg,
      Weighted_cum_maps : ( real * cum_map_data ) list ) : real list =
let
  val Order_nos = 
    map( fn( _, Cum_map ) => order_no( X, Cum_map ), Weighted_cum_maps )

  val Weighted_order_nos = map( fn( ( Weight, _ ), Order_no ) =>
      real Order_no / Weight,
      combine( Weighted_cum_maps, Order_nos ) )
  val Weighted_order_nos = 
    cmpsort( real_compare, Weighted_order_nos )
in
(*
  p"\n\n X = "; 
  print_req_node( order_no_arg_req_node X );
  p"\nOrder_nos = "; print_int_list Order_nos;
  p"\nWeighted_order_nos = "; print_real_list Weighted_order_nos;
*)
  Weighted_order_nos
end




datatype merged_node =
    cum_req_node of real list * cum_req_node ref
  | cum_eval_pq_node of real list * cum_eval_pq_node ref
  | cum_interval of real list * cum_interval ref

fun merged_node_weight( cum_req_node( X, _ ) ) = X
  | merged_node_weight( cum_eval_pq_node( X, _ ) ) = X
  | merged_node_weight( cum_interval( X, _ ) ) = X

exception Merged_node_cmp_exn
fun merged_node_cmp( X, Y ) =
  let
    val Xs = merged_node_weight X
    val Ys = merged_node_weight Y
  in
    list_compare( real_compare, Xs, Ys )
  end
   
fun find_set( cmp : '1a * '1a -> order, Xs : '1a splay list ) 
    : '1a splay =
  let
    val So_far = ref SplayNil
  in
    loop( fn Ys =>
      S.loop( fn Y => 
        case S.peek( cmp, Y, !So_far ) of
          ( NONE, Zs ) => So_far := S.insert( cmp, Y, Zs )
        | ( SOME _, Zs ) => So_far := Zs,
        Ys ),
      Xs );
    !So_far
  end


fun pq_multiplicity( eval_pq_cmp, Rn, 
      PQ_copy_ref : eval_pq_node splay ref ) : int =
  case S.peek( eval_pq_cmp, dummy_eval_pq_node Rn, !PQ_copy_ref ) of
    ( NONE, Xs ) => ( PQ_copy_ref := Xs; 0 )
  | ( SOME( _, N_ref ), Xs ) => ( PQ_copy_ref := Xs; !N_ref )
  
fun req_pq_to_eval_pq( eval_pq_cmp,
      RPQ : req_node splay ) : eval_pq_node splay ref =
  let
    val So_far : eval_pq_node splay ref = ref SplayNil
    fun insert New =
      case S.peek( eval_pq_cmp, New, !So_far ) of
        ( SOME( _, N_ref ), Xs ) => ( inc N_ref; So_far := Xs )
      | ( NONE, Xs ) => So_far := S.insert( eval_pq_cmp, New, Xs )
  in
    S.loop( fn Rn => insert( ref Rn, ref 1 ), RPQ );
    So_far
  end


fun req_pq_eval_pq_merge( eval_pq_cmp, REQ_PQ_ref, Eval_PQ_ref ) =
  let
    val So_far : eval_pq_node splay ref = ref SplayNil
    fun g Eval_PQ =
      S.loop( fn New as ( _, M_ref ) =>
        case S.peek( eval_pq_cmp, New, !So_far ) of
          ( SOME( _, N_ref ), Xs ) => (
              N_ref := !N_ref + !M_ref;
              So_far := Xs )
        | ( NONE, Xs ) => So_far := S.insert( eval_pq_cmp, New, Xs ),
        Eval_PQ )
  in
    g( !(req_pq_to_eval_pq( eval_pq_cmp, !REQ_PQ_ref )) );
    g( !Eval_PQ_ref );
    So_far
  end


fun print_eval_pq_node( Rn_ref, N_ref ) = (
  print_req_node( !Rn_ref );
  p( "   N_ref = ref " ^ Int.toString( !N_ref ) )
  )
fun print_interval_node( Lower, Upper, N_ref ) = (
  p( " \nLower = " ); print_req_node Lower; nl();
  p( " \nUpper = " ); print_req_node Upper; nl();
  p( "N_ref = " ^ Int.toString( !N_ref ) ^ "\n" )
  )

fun print_req_pq( RPQ : req_node splay ) =
  S.loop( fn X => (nl(); print_req_node X), RPQ )

fun print_eval_pq( EPQ ) =
  S.loop( print_eval_pq_node, EPQ )

fun print_maps( Maps : map_data list ) : unit =
loop( fn{ req_pq = ( REQ_PQ_ref, _ ),
          eval_pq = ( Eval_PQ_ref, _ ), ... } => (
  p"\n\nreq_pq =\n";
  print_req_pq( !REQ_PQ_ref );
  p"\n\neval_pq =\n";
  print_eval_pq( !Eval_PQ_ref );
  nl() ),
  Maps )


exception Total_eval_pq_exn
fun total_eval_pq( Maps as { eval_pq_cmp, ... } :: _ : map_data list ) =
  let
    val So_far : eval_pq_node splay ref = ref SplayNil
    fun g Eval_PQ =
      S.loop( fn New as ( _, M_ref ) =>
        case S.peek( eval_pq_cmp, New, !So_far ) of
          ( SOME( Old as ( _, N_ref ) ), Xs ) => (
              N_ref := max2( op<, !M_ref, !N_ref );
              So_far := Xs )
        | ( NONE, Xs ) => So_far := S.insert( eval_pq_cmp, New, Xs ),
        Eval_PQ )
  in
    loop( fn{ req_pq = ( REQ_PQ_ref, _ ), 
              eval_pq = ( Eval_PQ_ref, _ ), ... } =>
      g( !(req_pq_eval_pq_merge( eval_pq_cmp, REQ_PQ_ref, Eval_PQ_ref )) ),
      Maps );
    So_far
  end



exception Merge_exn
fun merge( Maps as Map :: _ : map_data list ) : map_data =
(*
  Computes cardinalities for eval PQ and interval nodes.
  The interval nodes are only taken from #ladder Map.
  Note that node order in the returned map is insignificant.
*)
let
  val _ = 
    if forall( fn M => !(#no_of_insertions M ) = !(#no_of_insertions Map),
         tl Maps )
    then
      ()
    else
      raise Merge_exn
  val { pe_cmp, req_pq_cmp, eval_pq_cmp, interval_cmp, pe_diff_cmp,  
        req_pq = ( MapRPQ, _ ), eval_pq = ( MapEPQ, _ ),  ... } = Map
  
  val REQ_PQ' = find_set( req_pq_cmp,
    map( fn{ req_pq = ( REQ_PQ_ref, _ ), ... } => !REQ_PQ_ref, Maps ) )

  val Eval_PQ' = S.map( fn( Rn_ref, _ ) => ( Rn_ref, ref 0 ),
    find_set( eval_pq_cmp,
      map( fn{ eval_pq = ( Eval_PQ_ref, _ ), ... } => !Eval_PQ_ref, Maps ) ) )

  val REQ_PQ_ref = ref REQ_PQ'
  val Eval_PQ_ref = ref Eval_PQ'

  val Intervals : Ladder.interval splay =
    S.map( fn( Lower, Upper, N_ref ) => ( Lower, Upper, ref( !N_ref ) ),
      Ladder.get_intervals( #ladder Map ) )

  val Total_eval_pq = total_eval_pq Maps
  fun old_count Rn = pq_multiplicity( eval_pq_cmp, Rn, Total_eval_pq )

  val REQ_PQ_copy =
    req_pq_to_eval_pq( eval_pq_cmp, !REQ_PQ_ref )
  fun REQ_PQ_count Rn = pq_multiplicity( eval_pq_cmp, Rn, REQ_PQ_copy )

  val MapRPQ_copy = req_pq_to_eval_pq( eval_pq_cmp, !MapRPQ )
  fun MapRPQ_count Rn = pq_multiplicity( eval_pq_cmp, Rn, MapRPQ_copy )

  val _ = S.loop( fn( Rn_ref, N_ref ) => case !Rn_ref of Rn =>
    N_ref :=  (
    let
      val M1 = old_count Rn
      val M2 = REQ_PQ_count Rn
    in
(*
      nl(); print_req_node Rn;
      p( "\n M1, M2 = " ^ Int.toString M1 ^ " " ^ Int.toString M2 );
*)
      M1 - M2
    end ),
    !Eval_PQ_ref )

  exception Multiplicity_difference_exn
  fun multiplicity_difference( Rn ) : int =
  let
    val New = 
      REQ_PQ_count Rn + pq_multiplicity( eval_pq_cmp, Rn, Eval_PQ_ref )
    val Old = 
      MapRPQ_count Rn + pq_multiplicity( eval_pq_cmp, Rn, MapEPQ )
  in
    if New <= 0 orelse Old < 0 orelse New < Old orelse 
       New <> Old andalso Old > 0
    then (
      p( "\n\nNew = " ^ Int.toString New ^"\n");
      p( "Old = " ^ Int.toString Old ^"\n");
      print_req_node Rn;

      raise Multiplicity_difference_exn
      )
    else
      New - Old
  end

  exception Update_n_ref_exn
  exception Not_map_member_exn
  fun update_n_ref( Rn, Delta : int, Intervals_ref ) : unit =
    if Delta < 0 then
      raise Update_n_ref_exn
    else if Delta = 0 then
      ()
    else
    let
      val ( SOME( Lower, Upper, N_ref ), Intervals ) =
        S.glb( interval_cmp, ( Rn, Rn, ref 0 ), !Intervals_ref )
      val _ = Intervals_ref := Intervals
    in
(*
        p( " \nRn =\n\n " );
        print_req_node Rn; nl();
        p( "Delta = " ^ Int.toString Delta ^"\n");
        p( " \nLower, Upper =\n\n " );
        print_req_node Lower; nl();
        print_req_node Upper; nl();
        p( "N_ref = " ^ Int.toString( !N_ref ) ^ "\n" );
*)
      N_ref := !N_ref - Delta;
      (
      if false (* not( map_member( Rn, Map, Intervals_ref ) ) *) then (
(*
        p"\n\nPrinting MapEPQ:\n";
        loop( fn X => ( print_eval_pq_node X; nl() ), S.inorder( !MapEPQ ) );
*)
        p"\n\nPrinting Intervals:\n";
        loop( fn X => ( print_interval_node X; nl() ), 
          S.inorder( !Intervals_ref ) );
        p( "\nIntervals is sorted = " ^
          Bool.toString( cmp_is_sorted( interval_cmp, 
                           S.inorder( !Intervals_ref ) ) ) ^ 
          "\n" );
        raise Not_map_member_exn
        )
      else if !N_ref < 0 then (
        p"\n\nPrinting MapEPQ:\n";
        loop( fn X => ( print_eval_pq_node X; nl() ), S.inorder( !MapEPQ ) );
        raise Update_n_ref_exn 
        )
      else 
        ()
       )
    end

  val Intervals_ref = ref Intervals

  val Es = !(req_pq_eval_pq_merge( eval_pq_cmp, REQ_PQ_ref, Eval_PQ_ref ))
  
  val _ = S.loop( fn( Rn_ref, _ ) => case !Rn_ref of Rn => 
      update_n_ref( Rn, multiplicity_difference Rn, Intervals_ref ),
    Es )

in 
  Eval_PQ_ref := S.filter(
    fn ( _, N_ref ) : eval_pq_node => !N_ref <> 0,
    !Eval_PQ_ref );
  Intervals_ref := S.filter(
    fn ( _, _, N_ref ) : Ladder.interval => !N_ref <> 0,
    !Intervals_ref );
  {
  first = false,
  no_of_insertions = ref( !( #no_of_insertions Map ) ),
  pe_cmp = pe_cmp, req_pq_cmp = req_pq_cmp, eval_pq_cmp = eval_pq_cmp,
  interval_cmp = interval_cmp, pe_diff_cmp = pe_diff_cmp,
  req_pq = ( REQ_PQ_ref, ref( S.no_of_nodes( !REQ_PQ_ref ) ) ),
  eval_pq = ( Eval_PQ_ref, ref( S.no_of_nodes( !Eval_PQ_ref ) ) ),
  ladder = Ladder.dummy_ladder( !Intervals_ref ) }
end (* fun merge *)



fun req_pq_prefix( Merged_nodes : merged_node list ) : req_node list =
  map( fn cum_req_node( _, Node_ref ) => 
    case !Node_ref of( _, Req_pq_node ) => Req_pq_node,
    takewhile( fn cum_req_node _ => true | _ => false,
      Merged_nodes ) )
(*
  Assume that N is the length of the list Xs returned by req_pq_prefix.
  N is used to determine if a second REQ run is needed. If N is less
  than or equal to the highest order number needed, the second run
  is not needed and Xs is used to emit REQs.
*)
  


fun reqs_and_multiplicities( Merged_nodes : merged_node list ) 
    : ( req_node * int ) list =
  filter( fn( _, N ) => N > 0,
  flat_map( 
    fn cum_req_node( _, Node_ref ) => (
         case !Node_ref of( _, Rn ) => 
           [ ( Rn, 1 ) ]
           )
     | cum_eval_pq_node( _, Node_ref ) => (
         case !Node_ref of ( _, _, ( Rn_ref, N_ref ) ) =>
           [ ( !Rn_ref, !N_ref ) ]
           )
     | cum_interval( _, Node_ref ) => (
         case !Node_ref of ( _, _, ( Lower, Upper, N_ref ) ) =>
         case !N_ref of N =>
           [ ( Lower, N div 2 ), ( Upper, N - N div 2 ) ]
           ),
     Merged_nodes ) )



exception Merged_cum_map_exn
fun merged_cum_map( Merged_map : map_data,
      Weighted_cum_maps : ( real * cum_map_data ) list,
      Best_in_random_ladder : real list )
    : cum_map_data * req_node list * ( req_node * int ) list =
let
 (* val () = (nl(); print_real_list Best_in_random_ladder; nl() ) *)

  val To_be_deleted = ~247861543 (* Random sentinel *)

  fun keep( Xs : real list ) : bool =
    case list_compare( real_compare, Xs, Best_in_random_ladder ) of
      LESS => true
    | _ => false

  val PQ = ref( [] : merged_node list )
  fun insert( Y : merged_node ) : unit = PQ := Y :: !PQ 

  val Deleted = ref( [] : merged_node list )
  fun insert_deleted( Y : merged_node ) : unit = Deleted := Y :: !Deleted 

  val Cum_merged_map as { cum_req_pq, cum_eval_pq, cum_intervals, ... } =
    make_cum_map_data( false, Merged_map )

  val So_far_ref = ref 0
in
(*  p"\n\nInserting cum_req_pq.\n\n"; *)
  S.loop( fn Node as ( Order_no_ref, Rn ) => 
    let
      val Xs = merged_order_no( start_at_req_pq Rn, Weighted_cum_maps )
    in
      if keep Xs then
        insert( cum_req_node( Xs, ref Node ) )
      else (
        Order_no_ref := To_be_deleted;
        insert_deleted( cum_req_node( Xs, ref Node ) ) )
    end,
    !cum_req_pq );

  cum_req_pq := S.filter( fn( Order_no_ref, _ ) => 
    !Order_no_ref <> To_be_deleted,
    !cum_req_pq );

(*  p"\n\nInserting cum_eval_pq.\n\n"; *)
  S.loop( fn Node as ( Order_no_ref, _, ( Rn_ref, N_ref ) ) => 
    let
      val Xs = 
        merged_order_no( start_at_eval_pq( !Rn_ref ), Weighted_cum_maps )
    in
      if keep Xs then
        if !N_ref <= 0 then raise Merged_cum_map_exn else (
(*      p( "\neval pq node count = " ^ Int.toString( !N_ref ) ); *)
        insert( cum_eval_pq_node( Xs, ref Node ) ) )
      else (
        Order_no_ref := To_be_deleted;
        insert_deleted( cum_eval_pq_node( Xs, ref Node ) ) )
    end,
    !cum_eval_pq );

  cum_eval_pq := S.filter( fn( Order_no_ref, _ , _ ) => 
    !Order_no_ref <> To_be_deleted,
    !cum_eval_pq );

 (* p"\n\nInserting cum_intervals.\n\n"; *)
  S.loop( fn X as ( _, _, ( Lower, _, N_ref ) ) => 
    (* Note that Lower is the worst value. *)
    if !N_ref <= 0 then raise Merged_cum_map_exn else insert(
      cum_interval(
        merged_order_no( start_at_intervals Lower, Weighted_cum_maps ),
        ref X ) ),
      !cum_intervals );

  PQ := cmpsort( merged_node_cmp, !PQ );

(* Cumulate !PQ. *)
  loop(
    fn cum_req_node( Weight, Node_ref ) =>
      let
        val ( Order_no_ref, Rn ) = !Node_ref
      in
        inc So_far_ref;
        Order_no_ref := !So_far_ref;
(*
        p( "\nreq_node: Weight = " ^ Real.toString Weight ^ " Rn = " );
        print_req_node Rn; 
        p( "Order_no_ref = " ^ Int.toString( !Order_no_ref ) );
*)
        ()
      end
    | cum_eval_pq_node( Weight, Node_ref ) =>
      let
        val ( Start_ref, _, ( Rn_ref, N_ref ) : eval_pq_node ) = !Node_ref
      in
        if !N_ref < 0 then raise Merged_cum_map_exn else ();
        Start_ref := !So_far_ref + 1;
        So_far_ref := !So_far_ref + !N_ref;
(*
        p( "\neval_pq_node: Weight = " ^ Real.toString Weight ^ " Rn_ref = " );
        print_req_node( !Rn_ref ); nl();
        p( "N_ref = " ^ Int.toString( !N_ref ) ^ "\n" );
        p( "Start_ref = " ^ Int.toString( !Start_ref ) ^ "\n" );
*)
        ()
      end
    | cum_interval( Weight, Node_ref ) =>
      let
        val ( Start_ref, _, ( Lower, Upper, N_ref ) : Ladder.interval ) = 
          !Node_ref
      in
        if !N_ref < 0 then raise Merged_cum_map_exn else ();
(*
        p( "\ninterval: Weight = " ); print_real_list Weight;
        p( " \nLower, Upper =\n\n " );
        print_req_node Lower; nl();
        print_req_node Upper; nl();
        p( "N_ref = " ^ Int.toString( !N_ref ) ^ "\n" );
*)
        Start_ref := !So_far_ref + 1;
        So_far_ref := !So_far_ref + !N_ref;
(*      p( "!Start_ref = " ^ Int.toString( !Start_ref ) ); *)

        ()
      end,
    !PQ );
  #no_of_hits_so_far Cum_merged_map := 0; 
  ( Cum_merged_map, 
    req_pq_prefix( !PQ ), 
    reqs_and_multiplicities(
      cmpsort( merged_node_cmp,
        dropwhile( fn cum_req_node _ => true | _ => false, !PQ ) @ 
        !Deleted ) ) )
end (* fun merged_cum_map *)


structure RL = Random_ladder(
  struct
    type eval_type = Map_arg.eval_type
  end
  )

type data0 = RL.data0
type data2 = RL.data2

val empty_data0 = RL.mk_data

local

fun  dummy_req_node( E : Map_arg.eval_type ) : req_node =
  ( E, Map_arg.Dummy_REQ_record )

fun merged_map_member( E : Map_arg.eval_type,
      Map as { eval_pq_cmp, eval_pq = ( Xs_ref, Card_ref ), ... } : map_data
      ) : bool =
  case dummy_req_node E of Rn =>
  req_pq_member( Rn, Map ) 
    orelse (
  case S.peek( eval_pq_cmp, ( ref Rn, ref 0 ), !Xs_ref ) of
    ( SOME _, Xs ) => ( Xs_ref := Xs; true )
  | ( NONE, Xs ) => ( Xs_ref := Xs; false ) ) 


fun merged_cum_map_member( E : Map_arg.eval_type,
      Cum_map as { cum_eval_pq_cmp, cum_eval_pq, ... } : cum_map_data
      ) : bool =
  case dummy_req_node E of Rn =>
  cum_req_pq_member( Rn, Cum_map ) 
    orelse (
  case S.peek( cum_eval_pq_cmp, 
               ( ref 0, ref 0, ( ref Rn, ref 0 ) ), !cum_eval_pq ) 
  of
    ( SOME _, Xs ) => ( cum_eval_pq := Xs; true )
  | ( NONE, Xs ) => ( cum_eval_pq := Xs; false ) ) 

fun req_pq_eval_pq_card(
      Cum_map as { cum_req_pq, cum_eval_pq, ... } : cum_map_data
      ) : int =
  S.no_of_nodes( !cum_req_pq ) +
  int_sum( map( fn( Start, So_far, ( Rn_ref, Hits_ref ) ) => !Hits_ref,
    S.inorder( !cum_eval_pq ) ) )

fun reset_cum_map(
      Cum_map as { no_of_hits_so_far,
        cum_eval_pq, cum_intervals, ... } : cum_map_data
      ) : unit = (
  no_of_hits_so_far := 0;
  S.loop( fn( _, So_far, _ ) => So_far := 0, !cum_eval_pq );
  S.loop( fn( _, So_far, _ ) => So_far := 0, !cum_intervals )
  )


in

type make_merged_cum_map_range = {
  cum_merged_map : cum_map_data,
  n_req_pq_eval_pq : int,
  random_ladder : data2,
  weighted_cum_maps : ( real * cum_map_data ) list,
  req_pq_prefix : req_node list,
  other_reqs_and_mults : ( req_node * int ) list
  }

(* To be exported: *)

fun get_req_pq_prefix( MMR : make_merged_cum_map_range ) : req_node list =
  #req_pq_prefix MMR

fun get_other_reqs_and_mults( MMR : make_merged_cum_map_range ) 
    : ( req_node * int ) list =
  #other_reqs_and_mults MMR

fun make_merged_cum_map( 
      Weighted_maps : ( real * map_data ) list, D0 : data0 
      ) : make_merged_cum_map_range =
let
  val () = start_timer Map_timer
  val Weighted_cum_maps = map( fn( Weight, Map ) =>
    ( Weight, make_cum_map_data( true, Map ) ),
    Weighted_maps )

  val Merged_map = merge( map( #2, Weighted_maps ) )

  val D1 = RL.build_ladder1( D0, fn E =>
    merged_order_no( start_at_req_pq( dummy_req_node E ), Weighted_cum_maps ) ) 

  val Best_in_random_ladder : real list =
    RL.ladder1_min( RL.filter_ladder1( D1, Max_int, fn E =>
      not( merged_map_member( E, Merged_map ) ) ) )

  val () = loop( fn( _, Cum_map ) => reset_cum_map Cum_map, Weighted_cum_maps )

  val ( Cum_merged_map, Req_pq_prefix, Other_reqs_and_mults ) =
    merged_cum_map( Merged_map, Weighted_cum_maps, Best_in_random_ladder )

  val N = req_pq_eval_pq_card Cum_merged_map

  val D2 = RL.cumulate( RL.filter_ladder1( D1, N, fn E =>
    not( merged_cum_map_member( E, Cum_merged_map ) ) ) )

  val () = loop( fn( _, Cum_map ) => reset_cum_map Cum_map, Weighted_cum_maps )
in
  stop_timer Map_timer; {
    cum_merged_map = Cum_merged_map,
    n_req_pq_eval_pq = N,
    random_ladder = D2,
    weighted_cum_maps = Weighted_cum_maps,
    req_pq_prefix = Req_pq_prefix,
    other_reqs_and_mults = Other_reqs_and_mults }
end

end (* local *)



fun order_no( Rn : req_node, { cum_merged_map, n_req_pq_eval_pq,
      random_ladder, weighted_cum_maps, ... } : make_merged_cum_map_range 
      ) : int =
  let
    val () = start_timer Map_timer
    val Order_no_opt = order_no'( start_at_req_pq Rn, true, cum_merged_map )

    val No =
      case Order_no_opt of
        SOME No => No
     | NONE =>
     case merged_order_no( start_at_req_pq Rn, weighted_cum_maps ) of Xs =>
       RL.order_no( random_ladder, Xs ) + n_req_pq_eval_pq
  in
    stop_timer Map_timer;
    No
  end

val insert = fn( New as ( E, _ ), Maps, D0 ) => (
  insert( New, Maps );
  RL.receive( D0,E ) )
  
end (* functor Map *)

