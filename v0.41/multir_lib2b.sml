(*
  File: multir_lib2b.sml.
  Created: 1999-07-28.
  Modified: 1999-07-29.
  Copied from multir_lib2.sml
  Used by the multir_r coupling.
*)

functor MULTIR_lib2b_fn( R : R_sig ) :
sig

type req_node
type make_merged_cum_map_range

val print_req_node : req_node -> unit

val multir_synt_compl : Ast.dec * Ast_lib2.simple_R_record -> real
val multir_fingerprint : 
  Ast.dec * Ast_lib2.simple_R_record * Ast_lib.pos list -> real

val first_run :
  Ast.dec *
  ( ( (Ast.dec * Ast_lib2.atomic_trf_record list * 'a) -> unit ) -> unit ) *
  real
  ->
  ( make_merged_cum_map_range * ( req_node * int ) list ) option * 
  req_node list *
  real
(* The option is NONE iff no second run should be performed. *)

val second_run :
  Ast.dec *
  ( ( (Ast.dec * Ast_lib2.atomic_trf_record list * 'a) -> unit ) -> unit ) *
  make_merged_cum_map_range * req_node list *
  ( { order_no : int, req_node : req_node } -> unit )
  ->
  unit

val map_time : unit -> real

end =
struct

structure Evaluate = R.R_lib.Exp_synt.Synt_lib.Evaluate


type eval_type = { 
  synted_syntactic_complexity : real,
  syntactic_fingerprint : real
  }

fun syntactic_fingerprint( { syntactic_fingerprint, ... } : eval_type ) = 
  syntactic_fingerprint

structure Map_arg =
  struct
    val Version = "multir_lib2b.sml";
    type eval_type = eval_type

    val truncate_syntactic_complexities = fn( { 
          synted_syntactic_complexity,  syntactic_fingerprint } : eval_type )  
        : eval_type => { 
      synted_syntactic_complexity = 
        real( Real.trunc synted_syntactic_complexity ),
      syntactic_fingerprint = syntactic_fingerprint
      }

    fun print_eval( 
          { synted_syntactic_complexity, ...  } : eval_type ) = (
      Lib.p( Real.toString synted_syntactic_complexity )
      )
    
    val syntactic_fingerprint = syntactic_fingerprint

    type REQ_record = Ast_lib2.REQ_record

    val Dummy_REQ_record = Ast_lib2.Dummy_REQ_record

    val Max_REQ_storage = 
      Constants.Total_max_REQ_storage
  end (* structure Map_arg *)

structure Map = Map( Map_arg )

val map_time = Map.map_time    

open Lib List1 Ast Ast_lib Ast_lib2 Print R R.R_lib Map 

fun multir_synt_compl( D : dec,  Simple : simple_R_record ) : real =
  pos_syntactic_complexity( D, #synted_exp Simple, 
    #synted_exp_bottom_poses Simple, #top_pos Simple )

fun multir_fingerprint( D : dec, Simple : simple_R_record, 
      Top_poses : pos list ) : real =
let
  val X = Evaluate.syntactic_fingerprint( apply_simple_R_record( D, Simple ) )
  val Y = list_hash( real o Word.toIntX o pos_hash, Top_poses )
in
  (X + 0.000000032335) * (Y + 0.000064674264)
end





fun find_MULTIRs( 
      D : dec,
      R_trf : ( (dec * atomic_trf_record list * 'a) -> unit ) -> unit,
      emit : Map.req_node -> unit
      ) : unit =
let
  fun emit_R( New_D, 
        [ R( Req_record as { r_top_poses = ( Alt, _ ), synted_exp, ...  }, 
             _ ) ],
         _  ) : unit = 
    if null Alt then (* Sentinel meaning identity R. *)
      ()
    else (
(*
      p"\n emit_R: synted_exp = "; Print.print_exp' synted_exp;
      nl();
*)
      case from_REQ_record Req_record of Simple :: _ =>
      emit( {
        syntactic_fingerprint = multir_fingerprint( D, Simple, Alt ),
        synted_syntactic_complexity = multir_synt_compl( D, Simple )
        },
        Req_record ) )
    handle Ex => (
    p"\n\nemit_R in find_MULTIRs:";
    raise Ex
    )

in
  R_trf emit_R
end (* fun find_MULTIRs *)


structure Make_maps :
  sig
    val weighted_maps :  unit -> ( real * map_data ) list 
  end =
struct

fun synted_compl_cmp( X : eval_type, Y : eval_type ) =
  real_compare( #synted_syntactic_complexity X, #synted_syntactic_complexity Y )


fun synted_compl_diff_cmp{ lower1 : eval_type, upper1 : eval_type,
      lower2 : eval_type, upper2 : eval_type } =
let
  fun s( X : eval_type ) = #synted_syntactic_complexity X
in
  real_compare(
    Real.abs( s lower1 - s upper1 ),
    Real.abs( s lower2 - s upper2 ) )
end

fun weighted_maps() = 
  [
  ( 1.0, empty_map( false, synted_compl_cmp, synted_compl_diff_cmp ) )
  ]

end (* structure Make_maps *)


fun print_eval_type( { synted_syntactic_complexity, ...  } : eval_type) 
    : unit = (
  p( "\nsynted_syntactic_complexity = " ^ 
    Real.toString synted_syntactic_complexity );
  nl(); nl()
  )
     
  
fun print_req_node( Eval, Rn ) = (
  (* nl(); nl(); *)
  print_eval_type Eval (* ;
  print_R_record Rn *)
  )

local

structure F = FIFO_occurrence_checking

fun cmp( ( E1 : eval_type, _ ), ( E2 : eval_type, _ ) ) =
  real_compare(
    #synted_syntactic_complexity E1,
    #synted_syntactic_complexity E2 )

in (* local *)

fun run( 
      D : dec,
      R_trf : ( (dec * atomic_trf_record list * 'a) -> unit ) -> unit,
      emit : Map.req_node -> unit
      ) : unit = 
let
  val Data = F.new( cmp, Constants.Total_max_REQ_storage )
  val emit_to_queue = fn X => 
    case F.insert( syntactic_fingerprint( #1 X ), X, Data ) of
      NONE => ()
    | SOME X => emit X
in
  find_MULTIRs( D, R_trf, emit_to_queue );
  loop( emit, F.contents Data )
end

end (* local *)

fun first_run( 
      D : dec,
      R_trf : ( (dec * atomic_trf_record list * 'a) -> unit ) -> unit,
      Production_goal : real
      ) : ( Map.make_merged_cum_map_range * ( req_node * int ) list ) option *
          Map.req_node list * real =
let
  val D0 = Map.empty_data0()
  val Weighted_maps = Make_maps.weighted_maps()
  val Maps = map( #2, Weighted_maps )
  val REQ_card = ref 0
  (* val _ = p"\n\nfirst_run:\n\n"; *)
  fun ins X = ( 
    (* print_req_node X; *)
    inc REQ_card; 
    Map.insert( X, Maps, D0 ) 
    )
  val () = run( D, R_trf, ins )
  val REQ_card = !REQ_card
  val MMR = Map.make_merged_cum_map( Weighted_maps, D0 )
  val REQ_PQ_prefix = Map.get_req_pq_prefix MMR
  val Reqs_and_mults = Map.get_other_reqs_and_mults MMR
  val N = real( length REQ_PQ_prefix )
  val Production = N + real_sum( map( fn(_,N) => real N, Reqs_and_mults ) )
  val Needed = N < Production - 0.5
in
  ( if Needed then SOME( MMR, Reqs_and_mults ) else NONE, 
    REQ_PQ_prefix,
    Production )
end (* fun first_run *)
  

structure S = Real_set

fun second_run( 
      D : dec,
      R_trf : ( (dec * atomic_trf_record list * 'a) -> unit ) -> unit,
      MMR, REQ_PQ_prefix,
      emit : { order_no : int, req_node : Map.req_node } -> unit
      ) : unit =
let
  fun fp( ( Eval, _ ) : Map.req_node ) =
    syntactic_fingerprint Eval
  val Fingerprints : real list = map( fp, REQ_PQ_prefix )
  val Fingerprints : S.set = S.list_to_set Fingerprints
  fun ok( ( Eval, _ ) : Map.req_node ) =
    not( S.member( syntactic_fingerprint Eval, Fingerprints ) )
  fun no REQ_node = Map.order_no( REQ_node, MMR )
  fun emit'( REQ_node as ( Eval, _ ) )=
    if ok REQ_node then
      emit{ order_no = no REQ_node, req_node =  REQ_node }
    else
      ()
in
  run( D, R_trf, emit' )
end (* fun second_run *)
  
type req_node = Map.req_node
type make_merged_cum_map_range = Map.make_merged_cum_map_range


end (* functor MULTIR_lib2b_fn *)
