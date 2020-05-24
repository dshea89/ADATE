(* File: abstr.sml
   Created in 040-version 1998-02-25.
   Modified 1999-08-15.
*)

functor Abstr( Synt_lib : SYNT_LIB ) :
sig
  val ABSTR_trfs : Ast.dec * { emb_coupled : bool, cost_limit : real } list *
        ( Ast_lib.pos -> bool ) * ( Ast_lib.pos list -> bool ) *
        ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list -> unit )
      -> unit
end =
struct


open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib6

structure Choose_arguments = Choose_arguments( Synt_lib )

fun time_limit Cost_limit = Cost_limit * Synt_lib.synt_and_eval_time_per_exp()
fun astpe() = Synt_lib.approximate_synt_time_per_exp()

local

structure H = Heap_functor(
  struct
    type elem = int * int * pos
    val op< = fn( (Nb1 : int, S1 : int, Top_pos1), (Nb2, S2, Top_pos2) ) => 
      Nb1 < Nb2 orelse ( Nb1 = Nb2 andalso S1 < S2 )
  end )

open Choose_arguments

in

fun top_pos_count( Dynamic : bool, Embedding : bool, E : exp, Data : data,
      Cost_limit : real, top_pos_ok : pos -> bool, 
      emit : bool * bool * pos * int * real -> unit
      ) : int =
let
(*
  val _ = (
    p"\n\ntop_pos_count:\n";
    p"Dynamic = "; p( Bool.toString Dynamic ); nl();
    p"Embedding = "; p( Bool.toString Embedding ); nl();
    p"Cost_limit = "; p( Real.toString Cost_limit ); nl(); nl()
    )
*)
  fun nb Top_pos = no_of_choices( Dynamic, Embedding, Data, Top_pos,
    time_limit Cost_limit, astpe() )
  val PQ = ref H.heap_nil
  val Leaves = absolutely_all_poses_filter(
    fn app_exp{ args = [], ... } => true | _ => false,
    E )
  fun pq_insert Pos = PQ := H.heap_insert(
    if top_pos_ok Pos then 
      ( nb Pos, exp_size( pos_to_sub( E, Pos ) ), Pos ) 
    else 
      ( 0, exp_size( pos_to_sub( E, Pos ) ), Pos ),
    !PQ )
  val _ = loop( fn Pos => pq_insert Pos, Leaves )
  val Chosen =  Pos_set.empty()
  fun update( Newly_chosen_node : pos, Nb : int ) : unit = (
    Pos_set.insert( Newly_chosen_node, Chosen );
    if not(null Newly_chosen_node) andalso
       forall( fn Child => Pos_set.member( Child, Chosen ),
         children( lt Newly_chosen_node, E ) )
    then
      pq_insert( lt Newly_chosen_node )
    else
      () )
  val Nc = ref 0
  val Nb_max = ref 0
  val S_max = ref 0
  fun g() =
    case H.heap_delete_min( !PQ ) of
      NONE => ()
    | SOME( ( Nb, S, Top_pos ), Heap ) => (
    PQ := Heap;
    Nb_max := max2( op<, Nb, !Nb_max );
    S_max := max2( op<, S, !S_max );
    let
      val Cutoff_cost =
        real( !Nc + 1 ) * real( max2( op<, !Nb_max, !S_max ) )
    in
    (* p"\n         Cutoff_cost = "; p( Real.toString Cutoff_cost ); nl(); *)
(* Cutoff_cost is and must be guaranteed to grow strictly monotonically. *)
    if Cutoff_cost > Cost_limit then
      ()
    else (
      if Nb > 0 then (
        (* p( "\nCutoff_cost = " ^ Real.toString Cutoff_cost ); *)
        emit( Dynamic, Embedding, Top_pos, Nb, Cutoff_cost );
        inc Nc 
        )
      else 
        ();
      update( Top_pos, Nb );
      g() )
    end )
  val _ = g()

in
  !Nc
end (* top_pos_count *)

end (* local *)
  
exception Zero_count_elim_exn

fun zero_count_elim( count : ''a * real -> int,
     Dynembs_and_widths : ( ''a * real ) list
     ) : ( ''a * (int*real) )list =
(* Repeatedly eliminate the first zero-count dynemb. *)
  if null Dynembs_and_widths then [] else
let
  val () = 
    if real_eq( real_sum( map( #2, Dynembs_and_widths ) ), 1.0 ) then
      ()
    else
      raise Zero_count_elim_exn
  val Xs = map( fn( Dynemb, W ) => ( Dynemb, ( count(Dynemb,W), W ) ), 
                Dynembs_and_widths )
in
  if not( exists( fn( _, (Count,_) ) => Count=0, Xs ) ) then Xs else
let
  val ( Dynemb', (0,W') ) = hd( filter( fn( _, (Count,_) ) => Count=0, Xs ) )

  val Xs = filter( fn( Dynemb, (_,_) ) => Dynemb <> Dynemb', Xs )

  val Sum = real_sum( map( fn( _, (_,W) ) => W, Xs ) )
in
  zero_count_elim( count,
   map( fn( Dynemb, (_,W) ) => ( Dynemb, W + W/Sum * W' ), Xs ) )
end
end (* fun zero_count_elim *)

type x_type = {
  cost_limit : real,
  counts_and_widths : ( (bool*bool) * (int*real) )list }

val Dynembs_and_widths = [
  ( (false,false), 0.3*0.7 ),
  ( (false,true), 0.3*0.3 ),
  ( (true,true), 0.7*0.3 ),
  ( (true,false), 0.7*0.7 ) 
  ]

fun top_pos_counts( Program : dec, Arity : int, Cost_limits : real list,
      top_pos_ok : pos -> bool, bottom_poses_ok : pos list -> bool )
    : Choose_arguments.data * x_type list =
let
  val Data = Choose_arguments.init( Program, bottom_poses_ok, Arity )

  fun dyn_stat_counts( Cost_limit : real ) =
  let
    val top_pos_count = fn( (Dynamic,Embedding), Width ) =>
      top_pos_count( Dynamic, Embedding, 
        #exp Program, Data, Width*Cost_limit, top_pos_ok, 
        fn _ => () )
  in
    { cost_limit = Cost_limit,
      counts_and_widths = zero_count_elim( top_pos_count, Dynembs_and_widths ) 
      } 
  end

in 
  ( Data, map( dyn_stat_counts, Cost_limits ) )
end (* top_pos_counts *)
  

local

fun count_and_width( Dynamic, Embedding, X : x_type ) =
  case assoc_opt( (Dynamic,Embedding), #counts_and_widths X ) of
    NONE => ( 0, 0.0 )
  | SOME( Count, Width ) => ( Count, Width )

fun cost_opt( Dynamic : bool, Embedding : bool, Cutoff_cost : real,
      X as { cost_limit, ...  } : x_type,
      Nb : int, Abstr_kind : abstr_kind ) : real option =
let
  val ( Nc, Width ) = count_and_width( Dynamic, Embedding, X )
in
  if Nc = 0 then NONE else
let
  val Cost = real Nc * real Nb / Width
in
  if Cutoff_cost > Width * cost_limit then
    NONE
  else
    SOME( Cost / real( Choose_arguments.abstr_kind_weight Abstr_kind ) )
end
end

fun max_cost_limit( Dynamic : bool, Embedding : bool, Xs : x_type list ) =
  max( op<, map( 
    fn X as { cost_limit, ... } =>
    let
      val ( _, Width ) = count_and_width( Dynamic, Embedding, X )
    in
      Width * cost_limit
    end,
    Xs ) )

in (* local *)

exception Do_with_arity_exn

fun do_with_arity( Program : dec, Arity : int, Cost_limits : real list,
      top_pos_ok : pos -> bool, bottom_poses_ok : pos list -> bool,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : unit =
let
  val Check_widths = map( fn _ => ref 0.0, Cost_limits )
  (* Used only for correctness checking. *)
  fun update( Opts : real option list ) = (
    loop( fn( NONE, W ) => () | ( SOME Cost, W ) => W := !W + 1.0 / Cost,
      combine( Opts, Check_widths ) );
    Opts
    )
  val ( Data, Xs : x_type list  ) =
    top_pos_counts( Program, Arity, Cost_limits, top_pos_ok, bottom_poses_ok )
  fun emit_top_pos_and_nb( Dynamic, Embedding, Top_pos, Nb, Cutoff_cost ) =
  let
    fun emit_choice( D, Alts, Abstr_kind ) =
    let
      val Let_exp_pos = case Abstr_kind of abstre => lt Top_pos | _ => Top_pos
      val let_exp{ dec_list = [ { func, pat, ... } ], ...} =
        pos_to_sub( #exp D, Let_exp_pos )
    in
      emit( 
        D, 
        [ ABSTR{ let_exp_pos = Let_exp_pos, func = func, parameters_added =
            case Abstr_kind of
              abstre => (
                case pat of app_exp{ func = T, args, ... } =>
                if T <> TUPLE orelse length args < Arity then
                  raise Do_with_arity_exn
                else
                  take( Arity, args ) )
            | _ => var_exps_in_pat pat,
          abstr_kind = Abstr_kind } ],
        update( map( fn X => 
          cost_opt( Dynamic, Embedding, Cutoff_cost, X, Nb, Abstr_kind ), 
          Xs )) )
    end (* fun emit_choice *)
    handle Ex => (
      p"\n\nemit_choice in abstr.sml:\n";
      Print.print_dec' D;
      print_pos Top_pos;
      p("\n" ^ abstr_kind_to_string Abstr_kind ^ "\n" );
      re_raise( Ex, "emit_choice" ) )
  in
    Choose_arguments.choices( Dynamic, Embedding, Data, Top_pos, emit_choice,
      time_limit( max( op<, Cost_limits ) ), astpe() )
  end (* fun emit_top_pos_and_nb *)
  
  val top_pos_count = fn( Dynamic, Embedding ) => 
        top_pos_count( Dynamic, Embedding, #exp Program, Data, 
          max_cost_limit( Dynamic, Embedding, Xs ), 
          top_pos_ok, emit_top_pos_and_nb )

in
  top_pos_count( true, false );
  top_pos_count( true, true );
  top_pos_count( false, false );
  top_pos_count( false, true );
  if exists( fn W => not( real_eq( !W, 1.0 ) ) andalso 
                     not( real_rep_eq(!W, 0.0) ), 
       Check_widths )
  then
    raise Do_with_arity_exn
  else
    ()
end (* do_with_arity *) 
   
end (* local *)


exception ABSTR_trfs_exn

fun ABSTR_trfs(
      D : dec,
      Cost_limit_info : { emb_coupled : bool, cost_limit : real } list,
      top_pos_ok : pos -> bool, 
      bottom_poses_ok : pos list -> bool,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : unit =
let
  val _ = 
    if real_eq( 1.0, real_sum( map( #2, Constants.Arity_weights ) ) ) then
      ()
    else
      raise ABSTR_trfs_exn
  val Min_limit = 5.0
  fun emit_cost_limits( post_adjust, Arity, Cost_limits ) =
  let
    val Cost_limits = map( fn( { emb_coupled, ... }, Cost_limit ) =>
      if Cost_limit < Min_limit orelse not emb_coupled andalso Arity = 0 then
        0.0
      else
        Cost_limit,
      combine( Cost_limit_info, Cost_limits ) )
    val Emitted_list = map( fn _ => ref false, Cost_limits )
    fun emit'( D, Trf_history, Cost_opts ) = (
      loop( fn( Cost_opt, Emitted ) =>
        case Cost_opt of SOME _ => Emitted := true | NONE => (),
        combine( Cost_opts, Emitted_list ) );
      emit( D, Trf_history, post_adjust Cost_opts ) 
      )
  in
    do_with_arity( D, Arity, Cost_limits, top_pos_ok, bottom_poses_ok, emit' );
    map( fn X => if !X then 1.0 else 0.0, Emitted_list )
  end
in
  adjust_cost_limits( 
    emit_cost_limits, 
    map( #1, Constants.Arity_weights ),
    map( fn{ cost_limit, ... } => 
      ( cost_limit, map( #2, Constants.Arity_weights ) ), 
      Cost_limit_info ) )
end
handle Ex => (
  p"\n\nABSTR_trfs: D =\n";
  Print.print_dec' D;
  p"\nemb_coupled = "; print_bool_list( map( #emb_coupled, Cost_limit_info ) );
  p"\ncost_limit = "; print_real_list( map( #cost_limit, Cost_limit_info ) );
  p"\n\n";
  raise Ex )



end (* functor Abstr *)

