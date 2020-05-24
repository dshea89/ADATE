(* File: dupl.sml.
   Created 1999-07-10.
   Modified 1999-09-02.
*)

functor DUPL_fn( R_lib : R_lib_sig ) :
sig

val DUPL_trfs : Ast.dec * real list * real *
      ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list -> unit ) 
    -> unit
end =
struct

structure DUPL_lib = DUPL_lib1_fn( R_lib )

open Lib List1 Ast Ast_lib Ast_lib2 Print DUPL_lib

structure Map = Map(
struct
val Version = "dupl"
type eval_type = DUPL_record

fun truncate_syntactic_complexities( { synted_exp, top_pos, rhs_size, 
      fingerprint, synted_syntactic_complexity } : DUPL_record ) 
    : DUPL_record = {
  synted_exp = synted_exp,
  top_pos = top_pos,
  rhs_size = rhs_size,
  fingerprint = fingerprint,
  synted_syntactic_complexity = real( Real.trunc synted_syntactic_complexity )
  }

val print_eval = print_DUPL_record
  
fun syntactic_fingerprint( { fingerprint, ... } : DUPL_record ) =
  fingerprint

val Max_REQ_storage = Constants.Total_max_REQ_storage

type REQ_record = unit
val Dummy_REQ_record = ()

end )


fun pe_cmp( X : DUPL_record, Y : DUPL_record ) : order =
  real_compare( #synted_syntactic_complexity X, #synted_syntactic_complexity Y )

fun pe_diff_cmp( { lower1 : DUPL_record, upper1 : DUPL_record,
                   lower2 : DUPL_record, upper2 : DUPL_record } ) : order =
  real_compare( 
    abs( #synted_syntactic_complexity lower1 - 
         #synted_syntactic_complexity upper1 ),
    abs( #synted_syntactic_complexity lower2 - 
         #synted_syntactic_complexity upper2 ) )



fun first_run( 
      Synt_and_eval_time_per_exp,
      D : dec, 
      REQ_cost_limit : real
      ) : Map.make_merged_cum_map_range * ( DUPL_record * int ) list *
          DUPL_record list =
let
  val D0 = Map.empty_data0()
  val Weighted_maps = [ ( 1.0, Map.empty_map( false, pe_cmp, pe_diff_cmp ) ) ]
  val Maps = map( #2, Weighted_maps )
  val REQ_card = ref 0
  (* val _ = p"\n\nfirst_run:\n\n"; *)
  fun ins X = ( 
    inc REQ_card; 
    Map.insert( (X,()), Maps, D0 ) 
    )

  val () = find_dupls( Synt_and_eval_time_per_exp, D, REQ_cost_limit, ins )

  val REQ_card = !REQ_card
  val MMR = Map.make_merged_cum_map( Weighted_maps, D0 )
  val REQ_PQ_prefix = Map.get_req_pq_prefix MMR
  val Reqs_and_mults = Map.get_other_reqs_and_mults MMR
  val N = length REQ_PQ_prefix
in
  (* p"\n\ndupl.sml: first_run: REQ_card = "; print_int REQ_card; nl();nl();
  flush_out( !std_out ); *)
  ( MMR, map( fn( (X,()), N ) => ( X, N ), Reqs_and_mults), 
    map( fn( X, () ) => X, REQ_PQ_prefix ) )
end (* fun first_run *)
  
exception Dupl_exn1
fun cost( Order_no : int, { rhs_size, ... } : DUPL_record ) : real =
  if rhs_size <= 0 orelse Order_no < 0 orelse Order_no > Max_int-100 then 
    raise Dupl_exn1 
  else
let
  val Offset = 10
in
  real( Order_no + Offset ) / real rhs_size
end

fun interval_width( Cost_limit : real, K : real,
      REQs_and_mults : ( DUPL_record * int )list ) : real =
let
  val So_far = ref 0.0

  fun emit{ REQ_record, order_no } = 
  let
    val Cost = K * cost( order_no, REQ_record )
  in
    if Cost < Cost_limit then So_far := !So_far + 1.0 / Cost else ();
    !So_far < 1.1
  end
in
  REQ_lib.choices_in_reqs_and_mults( REQs_and_mults, ~Max_int, emit );
  !So_far
end
  
exception Dupl_exn2
exception Dupl_exn3

fun normalize_one( D: ('a,'b)d, Cost_limit : real,
      REQs_and_mults : ( DUPL_record * int )list ) : real option =
  case REQs_and_mults of
    nil => NONE
  | _::_ => if Cost_limit < 1.1 then NONE else
let
(*
  val () = (
    p"\nnormalize_one:\n";
    p"Cost_limit = "; print_real Cost_limit;
    nl();
    print_list( fn( { rhs_size, ... }, N ) => (
      p"\n( "; print_int rhs_size; p","; print_int N; p")" ),
      REQs_and_mults );
    nl(); nl(); flush_out( !std_out ) )
*)
   
  val Start = real( exp_size( #exp D )  ) * REQ_lib.K_bis( Cost_limit, 1 )
  val N = ref 0
  fun f K = ( inc N; interval_width( Cost_limit, K, REQs_and_mults ) - 1.0 )
  fun stop1 K = 
    if !N > 2000 then raise Dupl_exn3 else false

  fun stop( K1 : real, K2 ) : bool =
    if !N > 2000 then raise Dupl_exn3 else
    if K1 < 1.0E~99 orelse K2 < 1.0E~99 orelse
       K1 > 1.0E99 orelse K2 > 1.0E99
    then
      raise Dupl_exn2
    else
      Real.abs( K1 / K2 -1.0 ) < 1.0E~7
in
  case
    Eq_solve_lib.eq_solve_is_start'( stop1, stop, false, f, 0.05, Start )
  of
    NONE =>
      Eq_solve_lib.eq_solve_is_start'( stop1, stop, false, f, 0.20, Start )
  | X => X
end (* fun normalize_one *)

fun normalize( D: ('a,'b)d, Cost_limits : real list,
      REQs_and_mults : ( DUPL_record * int )list ) : real option  list =
  map( fn Cost_limit => normalize_one( D, Cost_limit, REQs_and_mults ),
    Cost_limits )

structure S = Real_set

fun DUPL_trfs( D : dec, Cost_limits : real list, 
      REQ_cost_limit : real,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : unit =
let
  val Synt_and_eval_time_per_exp = R_lib.Exp_synt.Synt_lib.synt_and_eval_time_per_exp()
  val ( MMR, Other_reqs_and_mults, PQ_prefix ) =
    first_run( Synt_and_eval_time_per_exp, D, REQ_cost_limit )
  
  val REQs_and_mults = map( fn Record => ( Record, 1 ), PQ_prefix ) @
    Other_reqs_and_mults

  val K_opts = normalize( D, Cost_limits, REQs_and_mults )
in
  if forall( is_NONE, K_opts ) then () else
let
  (* val () = p"\nNormalization succeeded\n" *)
  fun emit'( X : DUPL_record, Order_no : int ) =
  let
    val Cost = cost( Order_no, X )
    val Cost_opts = 
      map( fn NONE => NONE | SOME K => SOME( K * Cost ), K_opts )

    val Cost_opts = map( fn( NONE, _ ) => NONE | ( SOME Cost, Cost_limit ) =>
      if Cost < Cost_limit then SOME Cost else NONE,
      combine( Cost_opts, Cost_limits ) )

    val ( New_D, Selected_rhs_poses ) = apply_dupl( D, X )
  in
  if forall( is_NONE, Cost_opts ) then () else
    emit( 
      New_D, 
      [ DUPL{ top_pos = #top_pos X, synted_exp = #synted_exp X,
              selected_rhs_poses = Selected_rhs_poses } ],
      Cost_opts
      )
  end 
  val Fingerprints : real list = map( #fingerprint, PQ_prefix )
  val Fingerprints : S.set = S.list_to_set Fingerprints
  val REQ_card = ref 0
  fun emit2( X : DUPL_record ) =(
    inc REQ_card;
    if S.member( #fingerprint X, Fingerprints ) then (
(*
      p"\nRejecting\n";
      print_DUPL_record X 
*)    )
    else
      emit'( X, Map.order_no( (X,()), MMR ) )
    )
in
  loop( emit', indexize( PQ_prefix, 1 ) );
  if null Other_reqs_and_mults then
    ()
  else (
    find_dupls( Synt_and_eval_time_per_exp, D, REQ_cost_limit, emit2 )
    (* p"\n\ndupl.sml: REQ_card for second run = "; print_int( !REQ_card );
    flush_out( !std_out ) *)
    )
end
end (* fun DUPL_trfs *)
   
    













end (* functor DUPL_fn *)
