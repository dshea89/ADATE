(* File: compound_trf_synt_lib2.sml.
   Created: 1999-07-24.
   Modified: 1999-08-15.
   Contains coupling between MULTIR and R.
*)

functor MULTIR_R_functor( R : R_sig ) :
sig

val multir_r_time : unit -> real

val multir_r : Ast.dec * Ast_lib2.atomic_trf_record list * real list *
      ( ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list ) *
        Ast_lib2.atomic_trf_record list -> unit  ) ->
      unit

end =
struct
open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib3 Ast_lib6 Print

structure So_far = R.R_lib.So_far
structure Exp_synt = R.R_lib.Exp_synt

fun report( Ex, N ) = (
  p"\n\nEXCEPTION RAISED AT LOCATION NUMBER "; print_int N;
  flush_out( !std_out );
  raise Ex )


structure MULTIR_lib2b = MULTIR_lib2b_fn( R )
open MULTIR_lib2b

val Multir_r_timer = mk_timer "multir_r"

fun multir_r_time() = check_timer Multir_r_timer

local

exception Regress_exn1

fun regress'( Top_pos, 
      Simple as { top_pos, rel_bottom_poses, synted_exp_bottom_poses, ... }
      : simple_R_record ) : pos =
let
(*
  val () = (
    p"\n\nregress':\n";
    print_pos Top_pos; nl();
    print_simple_R_record Simple;
    nl() )
*)
  val [ ( Rel_bottom_pos, Synted_exp_bottom_pos ) ] =
    filter( fn( Rel, Synt ) => is_prefix( top_pos @ Synt, Top_pos ),
      combine( rel_bottom_poses, synted_exp_bottom_poses ) )

  val N = length top_pos + length Synted_exp_bottom_pos
  val () = if N > length Top_pos then raise Regress_exn1 else ()
  val Y = top_pos @ Rel_bottom_pos @ drop( N, Top_pos )
in
(*  p"\nreturns "; print_pos Y; nl();nl(); *)
  Y
end

exception Rs_exn

fun rs( Simple as { top_pos, ... } : simple_R_record, 
      Maintained : simple_R_record ) : simple_R_record = 
  if is_strict_prefix( top_pos, #top_pos Maintained ) then
    Simple
  else if top_pos = #top_pos Maintained then
let
  val regress = fn Pos => regress'( Pos, Maintained )
  val Absolute_bottom_poses =
    map( fn Rel => regress( top_pos@Rel ), #rel_bottom_poses Simple )
  val top_pos = regress top_pos
  val N = length top_pos
in {
  top_pos = top_pos,
  rel_bottom_poses = map( fn A => drop( N, A ), Absolute_bottom_poses ),
  synted_exp = #synted_exp Simple,
  synted_exp_bottom_poses = #synted_exp_bottom_poses Simple }
end
  else raise Rs_exn

fun reg_simples Simples =
  if null Simples then [] else
  let
    val Y = dh Simples
    val Xs = lt Simples
  in
    snoc( reg_simples( map( fn X => rs(X,Y), Xs ) ), Y )
  end

in (* local *)

fun regress( Top_pos : pos, Simples : simple_R_record list ) : pos =
let
  val Simples = 
    stable_sort ( fn(X,Y) => length( #top_pos X ) < length( #top_pos Y ) )
      ( filter( fn{ top_pos, ... } => is_prefix( top_pos, Top_pos ), Simples ) )

  val Simples = reg_simples Simples

  fun g[ Simple ] = regress'( Top_pos, Simple )
    | g( Simple :: Simples ) = regress'( g Simples, Simple )

  val Y = if null Simples then Top_pos else g Simples
in (*
  p"\n\nregress:\n";
  print_pos Top_pos; nl();
  print_simple_R_record_list Simples; nl();
  print_pos Y; nl();
*)
  Y
end
handle Ex => (
  p"\n\nregress:\n";
  print_pos Top_pos; nl();
  print_simple_R_record_list Simples;
  nl();
  re_raise( Ex, "regress" ) )

end (* local *)

fun regress_simple( Simple as { top_pos, ... } : simple_R_record, 
      Maintained : simple_R_record list ) : simple_R_record = 
let
  val regress = fn Pos => regress( Pos, Maintained )
  val Absolute_bottom_poses =
    map( fn Rel => regress( top_pos@Rel ), #rel_bottom_poses Simple )
  val top_pos = regress top_pos
  val N = length top_pos
in {
  top_pos = top_pos,
  rel_bottom_poses = map( fn A => drop( N, A ), Absolute_bottom_poses ),
  synted_exp = #synted_exp Simple,
  synted_exp_bottom_poses = #synted_exp_bottom_poses Simple }
end
  


fun greater( D : dec, Rrec : R_record, Maintained : simple_R_record list,
      MultiRrecs : R_record list, Synted_compls : real list,
      Syntactic_fingerprints : real list ) : bool =
(* Returns true iff Rrec should be used. *)
  if null( #1( #r_top_poses Rrec ) ) then false else
let
  val regress = fn Pos => regress( Pos, Maintained )
  val New_syms = occurring_syms( #synted_exp Rrec )
  val Defined_syms = 
    Symbol_set.union_map( fn Rec => pat_syms( #synted_exp Rec ), MultiRrecs )
  val Intersection = Symbol_set.set_to_list( 
    Symbol_set.intersection( New_syms, Defined_syms ) )
in
  case filter( is_variable, Intersection ) of
    _::_ => true
  | [] =>
let
  val Simple :: _ = from_R_record Rrec
  val Simple = regress_simple( Simple, Maintained )
  val S = multir_synt_compl( D, Simple )
  val S_old = max( op<, Synted_compls )
in
  if S > S_old then
    true
  else if S < S_old then
    false
  else
let
  val Top_poses = map( regress, #1( #r_top_poses Rrec ) )
  val F = multir_fingerprint( D, Simple, Top_poses )

  val F_old = max( op<, Syntactic_fingerprints )
in
  F >= F_old
end
end
end (* fun greater *)
handle Ex => (
  p"\ngreater:\n";
  print_R_record Rrec; nl();
  print_simple_R_record_list Maintained; nl();
  report( Ex, 7 ) )


exception Alts_and_iws_exn
fun alts_and_iws( E : exp, top_pos_ok : pos list -> bool,
      Simples : simple_R_record list, Cost_limit : real ) : ( pos list * real )list =
let
  (* Copied from r.sml: *)
  val Alts : pos list list = filter( top_pos_ok,
    [ [] ] ::
    map( fn [ Alt ] => Alt, 
      produce_bottom_posess_list( E, [], 1,
        0.2 * Cost_limit * Exp_synt.Synt_lib.synt_and_eval_time_per_exp(),
        Exp_synt.Synt_lib.approximate_synt_time_per_exp()  ) ) )
(*
  val () = (
    p"\nAlts = ";
    print_list(fn Poses => (nl(); print_pos_list Poses), Alts );
    nl() )
*)
  val Alts = filter( fn [ _ ] => true | Poses as P::_::_ =>
    R.R_lib.common_scope_check( 
      pos_to_sub( E, P ),
      pos_to_sub( E, longest_common_prefix Poses ) ),
    Alts )

  fun f_size( S : real ) = 
    if S >= 1000.0 then real_pow( 1.2, 1000.0 ) else real_pow( 1.2, S)
  fun is_prefix_factor Poses =
  (* Penalize when only insertion is possible. *)
    if exists( fn Pos => 
         exists( fn{ top_pos, ... } => is_prefix( Pos, top_pos ), Simples ),
         Poses )
    then
      2.5
    else
      1.0

  val Sizes = map( fn Poses =>
      is_prefix_factor Poses *
      f_size( real( exp_size( pos_to_sub( E,
        longest_common_prefix( Poses @ map( #top_pos, Simples ) ) ) ) ) ),
    Alts )
  
  val Uniform_alt_width = 1.0 / real( length Alts )

  val Alpha = 1.0 / real_sum( map( fn S=> 1.0 / S, Sizes ) )
  val Iws = map( fn S=> 0.7 * Alpha / S + 0.3 * Uniform_alt_width, Sizes )
  val Xs = combine( Alts, Iws )
in
(*
  p"\nAlts_and_iws_and_sizes = \n";
    print_list(fn( ( Poses, Iw ), S ) => 
      (nl(); print_pos_list Poses; p" "; print_real Iw; p" "; print_real S), 
      combine( Xs, Sizes ) );
*)
  Xs
end (* fun alts_and_iws *)
handle Ex => report( Ex, 6 )

val Find_cost_limit_timer = mk_timer "find_cost_limit"

fun find_cost_limit( 
      Renamed_d_so_far,
      R_trf : real * (dec * atomic_trf_record list * 'a -> unit) -> unit,
      continue : unit -> bool,
      Production_goal : real
      ) : real * 
          ( make_merged_cum_map_range * (req_node*int)list ) option *
          req_node list *
          real =
if Production_goal < R.Min_replace_cost_limit + 1.0 then
  ( 0.0, NONE, [], 0.0 )
else
let
 (* val () = ( p"\nfind_cost_limit :"; print_real Production_goal; nl () ) *)
   
  val () = start_timer Find_cost_limit_timer
  fun g Cost_limit = (
(*    p"\n       Cost_limit = "; print_real Cost_limit; nl(); *)
    case first_run( Renamed_d_so_far, 
           fn emit => R_trf( Cost_limit, emit ), 
           Production_goal ) 
    of
      ( Opt, REQ_PQ_prefix, Production ) =>
    if Production > 5.0 * Production_goal orelse not( continue() ) orelse
       Cost_limit > 1.0E50
    then (
      stop_timer Find_cost_limit_timer;
      ( Cost_limit, Opt, REQ_PQ_prefix, Production )
      )
    else
      g( 2.0 * Cost_limit ) )
in
  g( 1.5 * Production_goal )
end (* fun find_cost_limit *)
handle Ex => report( Ex, 5 )

type alt_iw = { alt : pos list, iw : real, successor_iw_sum : real }

fun successor_iw_sum( Alts_and_iws : ( pos list * real )list ) : alt_iw list =
  case Alts_and_iws of
    [] => []
  | [ ( Alt, Iw ) ] => [ { alt = Alt, iw = Iw, successor_iw_sum = Iw } ]
  | ( Alt, Iw ) :: Alts_and_iws =>
  case successor_iw_sum Alts_and_iws of Ys as { successor_iw_sum, ... } :: _ =>
    { alt = Alt, iw = Iw, successor_iw_sum = Iw + successor_iw_sum } :: Ys


exception Deepening_r_exn

val Rest_timer = mk_timer "Rest_timer"

fun deepening_r( Renamed_d_so_far : dec, reverse_rename_R_record,
      Original_D : dec, Cost_limit : real, 
      top_pos_ok : pos list -> bool, So_far : Ast_lib2.so_far,
      Original_R_records : R_record list, R_trf, emit ) : real =
let
  val Emit_count = ref 0.0
  val Simples = map( fn Record =>
    case from_REQ_record Record of Simple :: _ => Simple,
    Original_R_records )
  val Complexities = map( fn Simple => 
    multir_synt_compl( Original_D, Simple ),
    Simples )
handle Ex => report( Ex, 10 )

  val Fingerprints = map( fn( Simple, Record ) =>
    multir_fingerprint( Original_D, Simple, #1( #r_top_poses Record ) ),
    combine( Simples, Original_R_records )  )
handle Ex => report( Ex, 20 )

  val Alts_and_iws = alts_and_iws( #exp( So_far.d_so_far So_far ),
    top_pos_ok, So_far.maintained_records So_far, Cost_limit )
handle Ex => report( Ex, 30 )

  val Alts_and_iws = sort (fn( (_,Iw1), (_,Iw2) ) => Iw1 < Iw2) Alts_and_iws

  val () = 
    if null Alts_and_iws then () else
    if not( real_eq( real_sum( map( #2, Alts_and_iws ) ), 1.0 ) ) then
      raise Alts_and_iws_exn
    else
      ()
  val Unused_iw = ref 0.0
  val Unused_real_iw = ref 0.0

  fun deepening_r{ alt, iw, successor_iw_sum } =
    case Cost_limit * iw of Production_goal =>
  let
(*
    val () = (
      p"\n\nAlt = "; print_pos_list Alt;
      nl(); flush_out( !std_out) )
*)
    val N = ref 0.0   
    val Used_real_iw = ref 0.0
    val Timer = mk_timer "deepening_r"
    val Max_time = 
      0.5 * Production_goal * Exp_synt.Synt_lib.synt_and_eval_time_per_exp()
(* Note that an ln Cost_limit factor could be introduced if Max_time were to
   be based on Adjusted_production_goal instead
*)
    fun continue() = check_timer Timer < Max_time

    fun ok R_record =
      greater( Original_D, reverse_rename_R_record R_record, 
        So_far.maintained_records So_far,
        Original_R_records, Complexities, Fingerprints )
handle Ex => report( Ex, 50 )

    val R_trf = fn( Cost_limit, emit ) => R_trf( alt, Cost_limit, emit )
handle Ex => report( Ex, 60 )

    val R_trf = fn( Cost_limit, emit ) =>
      R_trf( Cost_limit, fn( X as ( _, [ R( R_record, _ ) ], _ ) ) =>
        if ok R_record then emit X else () )
handle Ex => report( Ex, 70 )
   
    val () = start_timer Timer

    val Adjusted_iw = iw + iw / successor_iw_sum * (!Unused_iw)
    val Adjusted_real_iw = iw + iw / successor_iw_sum * (!Unused_real_iw)

    val Adjusted_production_goal = Cost_limit * Adjusted_iw
(*
    val () = (
      p"\nAdjusted_production_goal = "; print_real Adjusted_production_goal
      )
    val () = ( p"\n!Unused_real_iw = "; print_real(!Unused_real_iw) )
    val () = ( p"\nAdjusted_real_iw = "; print_real(Adjusted_real_iw) )
*)
    val ( Cost_limit, Opt, REQ_PQ_prefix, Production ) =
      find_cost_limit( Renamed_d_so_far, R_trf, continue, 
        Adjusted_production_goal ) 
handle Ex => report( Ex, 80 )
    
    val () = start_timer Rest_timer

    val K = (
      case REQ_lib.estimate_K( ceil Production, 
             ceil Production, Adjusted_production_goal, 1 )
      of
        NONE => REQ_lib.K_bis( Adjusted_production_goal, 1 )
      | SOME K => K )
handle Ex => report( Ex, 90 )

    fun cost( Order_no : int ) = K * ( real Order_no + real REQ_lib.Offset )

    val regr = fn Si => regress_simple( Si, So_far.maintained_records So_far )

(*
    fun new_so_far'( Simples, So_far ) = 
    let
      val  () = (
      p"\nnew_so_far': Simples = \n";
      loop( print_simple_R_record, Simples );
      nl();
      p"\nSo_far = \n"; print_so_far So_far )

      val SOME New_so_far = So_far.new_so_far'( Simples, So_far )
      val () = ( p"\nNew_so_far = \n"; print_so_far New_so_far; nl() )
    in
      SOME New_so_far
    end
*)

    fun emit'{ order_no = Order_no : int, 
          req_node = Req_node : req_node as ( _, R_record : R_record ) } = 
      case reverse_rename_R_record R_record of R_record => (
(*
      p"\n-----------------------------------------------------------\n";
      p"\nemit' in deepening_r:\n"; 
      print_R_record R_record; 
      p"\nd_so_far = \n"; Print.print_dec'( So_far.d_so_far So_far );
*)
      if real Order_no > Adjusted_production_goal then () else
      case So_far.new_so_far'( 
             map( regr, from_REQ_record R_record ),
             So_far ) handle Ex => report( Ex, 3 ) of
        NONE => ()
      | SOME New_so_far =>
      case R.R_lib2.make_emittable New_so_far 
           handle Ex => report( Ex, 4 ) 
      of ( New_D, CSE_info )=> (
(*
      p"\nNew d_so_far = \n"; Print.print_dec'( So_far.d_so_far New_so_far );
      p"\nNew_D  = \n"; Print.print_dec' New_D;
      p"\n-----------------------------------------------------------\n";
      flush_out(!std_out);
*)
        real_inc Emit_count; real_inc N;
        stop_timer Multir_r_timer;
        emit( New_D, [ R( R_record, #cse_records CSE_info ) ],  [
          case cost Order_no of Cost =>
            if Cost < Adjusted_production_goal then (
              Used_real_iw := !Used_real_iw + Adjusted_real_iw / Cost;
              SOME( max2( op<, 1.0, Cost / Adjusted_real_iw ) ) 
              )
            else 
              NONE ] );
        start_timer Multir_r_timer
        ) )
        
handle Ex => report( Ex, 40 )
  in
    loop( fn( REQ_node, I ) =>
      emit'{ order_no = I, req_node = REQ_node },
      indexize( REQ_PQ_prefix, 1 ) )
handle Ex => report( Ex, 100 );

    case Opt of
      NONE => ()
    | SOME( MMR, _ ) => (
(*        p"\nsecond run about to start.\n"; *)
        second_run( Renamed_d_so_far,
          fn emit => R_trf( Cost_limit, emit ), 
          MMR,
          REQ_PQ_prefix,
          emit' ) )
handle Ex => report( Ex, 110 );
(*
    p"ELEMENT";
    p"\n( "; print_real iw; p", "; print_real successor_iw_sum; p", ";
    print_real( !N ); p" ),\n";
*)
    Unused_iw := !Unused_iw * ( 1.0 - iw / successor_iw_sum ) +
      ( 1.0 - (!N)/Adjusted_production_goal ) * Adjusted_iw;
    Unused_real_iw := !Unused_real_iw * ( 1.0 - iw / successor_iw_sum ) + 
      (Adjusted_real_iw - !Used_real_iw);
    stop_timer Rest_timer;
    delete_timer Timer
  end (* fun deepening_r *)
in
  loop( deepening_r, successor_iw_sum Alts_and_iws );
  !Emit_count
end (* fun deepening_r *)

fun not_inside_synted_exp'( Top_pos, 
      { top_pos, synted_exp_bottom_poses, ... } : simple_R_record ) =
  if is_prefix( top_pos, Top_pos ) then
    case drop( length top_pos, Top_pos ) of Top_pos =>
      exists( fn Bpos => is_prefix( Bpos, Top_pos ), synted_exp_bottom_poses )
  else
    true

fun not_inside_synted_exp( Top_pos, Simples : simple_R_record list ) : bool =
  forall( fn Simple => not_inside_synted_exp'( Top_pos, Simple ), Simples )

structure H = Symbol_HashTable

exception Multir_r_exn1
exception Multir_r_exn2
fun multir_r( Original_D : dec,
      Trf_history as MULTIR{ so_far, original_r_records, new_min_once,
        top_pos_ok', poses_ok' } :: _ : atomic_trf_record list,
      Local_cost_limits as [ Cost_limit ] : real list,
      emit ) : unit =
let
(*
  val () = (
    p"\nmultir_r so_far =:\n"; print_so_far so_far; nl(); nl() )
*)    
  val () = start_timer Multir_r_timer
  val Maintained : simple_R_record list = So_far.maintained_records so_far
  val Originals : simple_R_record list = So_far.original_records so_far

  val regress = fn Pos => regress( Pos, Maintained )

  fun top_pos_ok( Top_poses : pos list ) = (
    forall( fn Top_pos => not_inside_synted_exp( Top_pos, Maintained ),
      Top_poses ) 
      andalso
    top_pos_ok'( map( regress, Top_poses ) ) )
  handle Ex => report( Ex, 2 )


  fun is_ok( Top_pos, Absolute_bottom_poses ) = 
  let
    val N = length Top_pos
    val () = 
      if exists( fn B => length B < N, Absolute_bottom_poses ) then
        raise Multir_r_exn1
      else
        ()
    val Bs = map( fn B => drop( N, B ), Absolute_bottom_poses )
  in
    So_far.independent'( Top_pos, Bs, Originals )
  end

  fun poses_ok Xss = (
    forall( fn( _, Bottom_poses ) =>
      forall( fn B => not_inside_synted_exp( B, Maintained ), Bottom_poses ),
      Xss ) andalso
    let
      val Xss =
        map( fn( Top_pos, Absolute_bottom_poses ) =>
          ( regress Top_pos, map( regress, Absolute_bottom_poses ) ),
          Xss )
    in
      poses_ok' Xss andalso forall( is_ok, Xss )
    end )
    handle Ex => report( Ex, 1 )
  
  val ( Renamed_d_so_far, Sym_subst ) =
    case reversible_rename( #exp( So_far.d_so_far so_far ) ) of 
      ( E, Sym_subst ) =>
        ( set_exp( So_far.d_so_far so_far, E ), Sym_subst )

  fun s E = apply_sym_subst_exp( E, Sym_subst )

  val U : symbol list H.hash_table = 
    Ast_lib3.symbol_hash_table_reverse Sym_subst

  fun mk_min_once_syms Sym =
    case H.find U Sym of
      NONE => [Sym]
    | SOME( Xs as _::_ ) => Xs

  val New_min_once = map( fn Syms =>
    flat_map( mk_min_once_syms, Syms ),
    new_min_once )

  fun R_trf( Alt, Cost_limit, emit ) =
    R.R_trfs_with_no_of_cases_distribution( 
      Exp_synt.Synt_lib.synt_and_eval_time_per_exp(),
      [ ( 0, 0.6 ), ( 1, 0.2 ), ( 2, 0.2 ) ],
      Renamed_d_so_far, SOME[ Alt ], [ Cost_limit ],
      top_pos_ok, poses_ok, New_min_once, true, emit )

  fun reverse_rename_R_record( { r_top_poses = ( Alt, Stand_in_opt ), 
        bottom_poses, bottom_labels, synted_exp, ... } : R_record ) 
      : R_record = { 
     r_top_poses = ( Alt,
                   case Stand_in_opt of
                     NONE => NONE
                   | SOME( Stand_in, Pos ) => SOME( s Stand_in, Pos ) ),
    bottom_poses = bottom_poses,
    bottom_labels = bottom_labels,
    synted_exp = s synted_exp,
    not_activated_syms = [] }
      
  val Emit_count : real =
    deepening_r( Renamed_d_so_far, reverse_rename_R_record, Original_D, 
      Cost_limit, top_pos_ok, 
      so_far, original_r_records, R_trf, fn X => emit( X, Trf_history ) );
in
(*
  p"\nmultir_r:\n";
  p"\n  Cost_limit = "; print_real Cost_limit;
  p"\n  Emit_count = "; print_real Emit_count; nl();
*)
  stop_timer Multir_r_timer
(* ;
  p"\nFind cost limit time = ";
  print_real( check_timer Find_cost_limit_timer );
  p"\nRest time = "; print_real( check_timer Rest_timer ) 
*)
end (* fun multir_r *)
handle Ex => (
  p"\nmultir_r:\n";
  p"\nOriginal_D =\n"; Print.print_dec' Original_D;
  p"\nTrf_history =\n"; print_trf_history Trf_history;
  p"\nCost_limit =\n"; print_real Cost_limit; nl();
  raise Ex )
  
  


end (* functor MULTIR_R_functor *)
