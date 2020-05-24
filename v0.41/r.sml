(* File: r.sml.
   Created 1998-03-25.
   Modified 2000-05-08.
Replacement of rconsts incorporated 2000-04-03.

2000-05-05: Spiked cost distribution for linear combinations.
 Alleviates problem with equivalent insertions into lin combs.

2000-05-08: NN post optimization added.
*)

signature R_sig =
sig

val R_trfs_with_no_of_cases_distribution : 
  real *
  ( int * real ) list *
  Ast.dec * 
  Ast_lib.pos list list option *
  real list *
  ( Ast_lib.pos list -> bool ) *
  ( ( Ast_lib.pos * Ast_lib.pos list ) list -> bool ) *
  Ast.symbol list list * 
  bool * 
  ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list -> unit) 
  -> unit

val R_trfs : 
  real *
  Ast.dec * 
  Ast_lib.pos list list option *
  real list *
  ( Ast_lib.pos list -> bool ) *
  ( ( Ast_lib.pos * Ast_lib.pos list ) list -> bool ) *
  Ast.symbol list list * 
  bool * 
  ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list -> unit) 
  -> unit

val sum_of_R_cost_limits : unit -> real
val no_emitted_by_R : unit -> int
val cum_R_time : unit -> real

val Min_replace_cost_limit : real

structure R_lib : R_lib_sig
structure R_lib2 : R_lib2_sig
end

functor R_fn( Exp_synt : EXP_SYNT ) : R_sig =
struct


val Min_replace_cost_limit = 8.0

structure R_lib = R_lib_fn( Exp_synt )

structure R_lib2 = R_lib2_fn( R_lib )

open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib6 Print R_lib

val R_timer = mk_timer "R_timer"

fun cum_R_time() = check_timer R_timer

fun stand_in( D : dec, Alt as Top_pos :: _ : pos list ) =
let
  val Root_top_pos = longest_common_prefix Alt
  val Subst = pos_to_pat_subst( true, true, D, Root_top_pos )
(* Each To must be unique to ensure that Subst can be inverted.
   Therefore, Require_var_pat is true in the call to pos_to_pat-subst. *)

  val Sub = pos_to_sub( #exp D, Top_pos )
in
  case assoc_opt'( exp_eq, Sub, Subst ) of
    NONE => NONE
  | SOME Stand_in =>
  case all_poses_in_preorder Stand_in of
    [ [] ] => NONE
  | _::_ => SOME( Stand_in, Subst )
end

local

fun apply_reverse_subst( Stand_in, Pos, Subst ) =
let
(*
  val () = (
    p"\nStand_in ="; Print.print_exp' Stand_in;
    p"\nPos = "; print_pos Pos;
    p"\nSubst = "; print_exp_subst Subst;
    nl() )
*)
  val Subst = map( fn( From, To ) => ( To, From ), Subst )
  val Sub = pos_to_sub( Stand_in, Pos )
  val V = gen_var_exp( get_exp_info Sub )
  val Stand_in = pos_replace( Stand_in, Pos, fn _ => V )
  val Stand_in = apply_exp_subst( Stand_in, Subst )
  val Result = pos_replace( Stand_in, Pos, fn _ => Sub )
in
(*
  p"\nResult = "; Print.print_exp' Result;
*)
  Result
end





fun stand_in_opt_to_r_top_poses_list( 
      Alt : pos list, 
      Opt 
      ) : r_top_poses list =
  case Opt of
    NONE => []
  | SOME( Stand_in, Subst ) =>
  let
    val [] :: Stand_in_poses = all_poses_in_preorder Stand_in
  in
(*    p"\n Alt = "; print_pos_list Alt; *)
    map( fn Pos => 
      ( Alt, SOME( apply_reverse_subst( Stand_in, Pos, Subst ), Pos ) ), 
      Stand_in_poses )
  end

in (* local *)

fun alt_list_to_r_top_poses_list( D : dec, Alts : pos list list ) 
    : r_top_poses list =
  flat_map( fn Alt => 
    ( Alt, NONE ) ::
    stand_in_opt_to_r_top_poses_list( 
      Alt,
      stand_in( D, Alt ) ),
    Alts )

end (* local *)

           
fun use_stand_in( D : dec, Alt : pos list, Stand_in : exp ) =
  case Alt of
    [] => D
  | P :: Alt => 
      use_stand_in( pos_replace_dec( D, P, fn _ => Stand_in ), Alt, Stand_in )


local 


fun case_rhs_weight( E, Spike_table, Top_pos ) =
  case Pos_hash.find Spike_table Top_pos of
    SOME W => W
  | NONE =>
  if null Top_pos orelse dh Top_pos=0 orelse
     exp_count(is_case_exp,pos_to_sub(E,lt Top_pos)) = 0 then
    1
  else if is_dont_know_exp(pos_to_sub(E,Top_pos)) then 
    4
  else 
    2

structure H = Heap_functor(
  struct
    type elem = int * int * r_top_poses
    val op< = fn( (S1 : int, W1 : int, Alt1), (S2, W2, Alt2) ) => 
      S1 < S2 orelse S1 = S2 andalso W1 > W2
  end )

in

fun top_pos_count( E : exp, R_top_poses_list : r_top_poses list, 
      Spike_table : int Pos_hash.hash_table,
      nb : r_top_poses -> int, 
      alt_size : r_top_poses -> int,
      Cost_limit : real, Min_replace_cost_limit : real, 
      emit : r_top_poses * int * int -> unit
      ) : int =
let
  val PQ = ref H.heap_nil
  val Nc = ref 0
  val R_top_poses_list = filter( fn X => nb X > 0, R_top_poses_list )
  val () = loop( fn X as ( Alt, _ ) =>
    PQ := H.heap_insert( 
            ( alt_size X, 
              max( op<, 
                   map( fn Top_pos => 
                     case_rhs_weight( E, Spike_table, Top_pos ), Alt ) ),
              X ), 
            !PQ ),
    R_top_poses_list )
  fun g() =
    case H.heap_delete_min( !PQ ) of
      NONE => ()
   | SOME( ( _, W, R_top_poses ), Heap ) => 
   let
     val Nb = nb R_top_poses
   in
     PQ := Heap;
     if Cost_limit * real W / real( !Nc + W ) / real Nb < Min_replace_cost_limit then
         ()
       else (
         Nc := !Nc + W;
         emit( R_top_poses, !Nc, W );
         g()
         ) 
   end
in
  g();
  !Nc
end (* top_pos_count *)

end (* local *)

local

exception Funcs_and_vars_at_pos
fun funcs_and_vars_at_pos(E:exp,Pos:pos) : symbol list * symbol list =
  let
    fun g _ = (nil,nil)
    fun f((Funcs,Vars),E_sub,P::_) =
      case E_sub of
        case_exp{rules,...} =>
          if P=0 then
            (Funcs,Vars)
          else
            ( Funcs, vars_in_pat(#pat(nth(rules,P-1)))@Vars )
      | let_exp{dec_list,...} =>
          if P<length dec_list then
            let val {func,pat,...} = nth(dec_list,P)
            in
              ( func::Funcs, vars_in_pat pat @ Vars )
            end
          else
            (Funcs,Vars)
      | _ => (Funcs,Vars)
  in
    pos_fold(f,g,Pos,E)
  end
  handle Ex => re_raise(Ex,"Funcs_and_vars_at_pos")

fun alt_hash( Xs : pos list ) : word =
  Word.fromInt( hash_real_to_int( 
    list_hash( real o Word.toIntX o pos_hash, Xs ) * 1.0E9 ) )

structure Alt_hash_key : HASH_KEY =
struct
  type hash_key = pos list
  val hashVal = alt_hash
  fun sameKey( X, Y : pos list ) = X = Y
end

structure Alt_hash = HashTableFn( Alt_hash_key )

in (* local *)

exception Nbr1_init_exn

fun nbr1_init() = Alt_hash.mkTable( 10, Nbr1_init_exn )

fun nbr1'(
      D as { func, pat, exp, dec_info } : dec,
      Alt : pos list,
      poses_ok : ( pos * pos list ) list -> bool
      ) : pos list =
(* Note that the returned positions are local w.r.t. H_E1. *)
let
  val Root_top_pos = longest_common_prefix Alt
  val ( Funcs, Vars ) =
    case funcs_and_vars_at_pos( exp, Root_top_pos ) of ( Funcs, Vars ) =>
      ( func :: Funcs, vars_in_pat pat @ Vars )

  val H_E1 = pos_to_sub( exp, hd Alt )
  fun bottom_pos_ok Bottom_pos =
    let
      val E1 = pos_to_sub( H_E1, Bottom_pos )
    in
      not( is_leaf E1 ) andalso
      poses_ok( map( fn Top_pos => 
        ( Top_pos, [ Top_pos @ Bottom_pos ] ), 
        Alt ) ) andalso
      Exp_synt.Synt_lib.scope_check( E1, Funcs, Vars )
    end
  val Bottom_poses =
    filter( bottom_pos_ok, proper_descendants( [], H_E1 ) )
in
  Bottom_poses
end (* nbr1' *)

fun nbr1( D, Alt, poses_ok, Memo_table ) : int =
  case Alt_hash.find Memo_table Alt of
    NONE =>
      let
        val N = length( nbr1'( D, Alt, poses_ok ) )
      in
        Alt_hash.insert Memo_table ( Alt, N );
        N
      end
  | SOME N => N

end (* local *)


local

(* Debugging version of replace: *)

(*
fun replace(Disallow_Old_E : bool, D as {func,pat,exp,dec_info} : Ast.dec,
    Top_pos : Ast_lib.pos, Bottom_poses : Ast_lib.pos list, 
    Cost_limit : real, Min_once : Ast.symbol list list, Eq_check : bool,
    emit ) : unit =
    loop( fn Cost =>
      emit( D, real Cost, [], { bottom_labels = [], synted_exp = Dummy_exp } ),
      fromto( 1, Real.round Cost_limit ) )
*)

exception Stand_in_only_to_be_used_with_R0

fun replace'( Synt_and_eval_time_per_exp,
      No_of_cases_distribution, NN_synt, D, emit, Limits_and_counts as [ _ ], 
      Min_once, Eq_check,
      R_top_poses as ( Alt, Stand_in_opt ),
      Nb, Bottom_poses, Nc, W ) =
(*
  It turns out to be unnecessary to run R_trfs with multiple cost limits.
  The code in this function assumes that there only is one cost limit.
*)
let
  val _ = 
    if is_SOME Stand_in_opt andalso not( null Bottom_poses) then
      raise Stand_in_only_to_be_used_with_R0
    else
      ()
  val Root_top_pos = longest_common_prefix Alt
  val D =
    case Stand_in_opt of
      NONE => D
    | SOME( Stand_in, _ ) => use_stand_in( D, Alt, Stand_in )
  val ( D, Top_pos ) =
    case Alt of
      [ Top_pos ] => ( D, Top_pos )
    | Top_pos :: _ :: _ => (
        set_exp( D,
          abstract_common_exp( #exp D,
            Root_top_pos,
            pos_to_sub( #exp D, Top_pos ) ) ), (* The common exp. *)
        Root_top_pos @ [ 0 ]
        )
  val Local_cost_limits = map( fn( Cost_limit, Top_pos_count ) =>
    if Nb = 0 orelse Top_pos_count = 0 then
      0.0
    else
      Cost_limit * real W / real Top_pos_count / real Nb,
    Limits_and_counts )
  
  val [ K ] =  map( fn Limit => REQ_lib.K_bis( Limit, 1 ), Local_cost_limits )

  val [ ( _, Top_pos_count ) ] = Limits_and_counts

  val Max_limit = max( op<, Local_cost_limits )

  fun emit'( D, Cost, Not_activated_syms, { bottom_labels, synted_exp } ) =
    emit( D,
       { r_top_poses = R_top_poses,
          bottom_poses = Bottom_poses,
          bottom_labels = bottom_labels,
          synted_exp = synted_exp,
          not_activated_syms = Not_activated_syms },
       [ 
         if K * ( Cost + real REQ_lib.Offset ) < Max_limit then
           SOME( real Top_pos_count * real Nb * 
                 ( Cost + real REQ_lib.Offset ) / real W * K )
         else
           NONE
         ]
      )


  val Top_pos =
    case Stand_in_opt of
      NONE => Top_pos
    | SOME( _, Local_pos ) => Top_pos @ Local_pos

  val ( Old_Es, Allowed ) = 
    case Stand_in_opt of
      SOME _ => ( [], [] )
    | NONE =>
    case stand_in( D, [ Top_pos ] ) of
      NONE => ( [], [] )
    | SOME( Stand_in, _ ) => ( [ Stand_in ], [ Stand_in ] )
  val Old_Es = pos_to_sub( #exp D, Top_pos ) :: Old_Es
in
  replace( Synt_and_eval_time_per_exp,
      No_of_cases_distribution, NN_synt, Old_Es, Allowed, D, Top_pos, 
     map( fn P => Top_pos @ P, Bottom_poses ),
     Max_limit, Min_once, Eq_check, emit' )
end (* replace' *)

in (* local *)

(* The three kinds of R are replacement with 0 bottom nodes, insertion and
   replacement with 1 bottom node and are numbered 0, 1 and 2 respectively.
*)
fun do_with_R_kind( Synt_and_eval_time_per_exp,
      No_of_cases_distribution, NN_synt : bool, R_kind : int, D : dec, 
      Cost_limits :  real list, 
      R_top_poses_list : r_top_poses list, 
      Spike_table : int Pos_hash.hash_table,
      poses_ok : ( pos * pos list ) list -> bool,
      Min_once :  symbol list list, Eq_check : bool,
      emit : dec * R_record * real option list -> unit
      ) : unit =
let
  val Memo_table = nbr1_init()
  fun nb( Alt, Stand_in_opt ) : int =
    if R_kind <> 0 andalso is_SOME Stand_in_opt then 0 else
    case R_kind of
      0 => if poses_ok( map( fn Top_pos => ( Top_pos, [ ] ), Alt ) ) then
             1
           else
             0
     (* Is actually always 0, but 1 is used to make top_pos_count work 
        properly *)

    | 1 => if is_leaf( pos_to_sub( #exp D, hd Alt ) ) orelse
              not( poses_ok( map( fn Top_pos => ( Top_pos, [ Top_pos ] ), 
                                  Alt ) ) ) 
           then 
             0 
           else 
             1
    | 2 => nbr1( D, Alt, poses_ok, Memo_table )

  fun alt_size( ( Alt as ( Top_pos :: _ ), _ ) : r_top_poses ) : int =
    length Alt * exp_size( pos_to_sub( #exp D, Top_pos ) )


  val Top_pos_counts = map( fn Cost_limit =>
    top_pos_count( #exp D, R_top_poses_list, Spike_table,
      nb, alt_size, Cost_limit, Min_replace_cost_limit, 
      fn _ => () ),
    Cost_limits )

  val Limits_and_counts = combine( Cost_limits, Top_pos_counts )

  fun emit'( R_top_poses as ( Alt, _ ), Nc, W ) =
    case nb R_top_poses of Nb =>
    loop( fn Bottom_poses =>
      replace'( Synt_and_eval_time_per_exp,
        No_of_cases_distribution, NN_synt, D, emit, 
        Limits_and_counts, Min_once, Eq_check, 
        R_top_poses, Nb, Bottom_poses, Nc, W ),
      case R_kind of
        0 => [ [] ]
      | 1 => [ [ [] ] ]
      | 2 => map( fn P => [ P ], nbr1'( D, Alt, poses_ok ) )
      )
in
  top_pos_count( #exp D, R_top_poses_list, Spike_table, nb, alt_size, 
    max( op<, Cost_limits ),
    Min_replace_cost_limit, emit' );
  ()
end (* do_with_R_kind *)

end (* local *)
 

val Sum_of_R_cost_limits = ref 0.0
fun sum_of_R_cost_limits() = !Sum_of_R_cost_limits

val No_emitted_by_R = ref 0
fun no_emitted_by_R() = !No_emitted_by_R


val R_kind_weights = [
  ( 2, 0.2 ),
  ( 1, 0.3 ),
  ( 0, 0.5 )
  ]

structure F = Ast_lib2.FIFO_occurrence_checking

fun cmp( 
      ( S1 : real, _ : R_record, _ : real option list), 
      ( S2 : real, _ : R_record, _ : real option list)  )
  =
  real_compare( S1, S2 )

exception R_trfs_exn1
exception R_trfs_exn2

fun R_trfs_with_no_of_cases_distribution( 
      Synt_and_eval_time_per_exp : real,
      No_of_cases_distribution : ( int * real )list,
      D : dec, 
      Alts_opt : pos list list option,
      Cost_limits : real list,
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool, 
      Min_once : symbol list list, Eq_check : bool,
      emit : dec * atomic_trf_record list * real option list -> unit ) : unit =
(* 
  Note that the domain of top_pos_ok is pos list instead of pos since R:s
  may be substitutive. The top_pos_ok predicate is needed only to quickly 
  eliminate irrelevant top positions. The poses_ok predicate could be used
  instead if efficiency didn't matter. Note that the domain of poses_ok also
  reflects the need to check substitutive R:s.

  Note that the emitted costs are normalized but that the number of decs
  produced equals the cost limit.
*)
let 
(*
  val () = ( p"\nR_trfs started "; print_real( hd Cost_limits );
             flush_out( !std_out ) )
*)
  val _ = start_timer R_timer
  fun report S = ()
(*
     ( p"\n"; p S; print_real( check_timer R_timer );  nl() )
*)
  val D as { exp, ... } = 
    if is_NONE Alts_opt then add_not_activated_exps_dec D else D
(*
  val () = (
    p"\nR_trfs_with_no_of_cases_distribution:\n";
    p"\nD = \n"; Print.print_dec' D; nl() )
*)
  val () = if is_not_activated_exp exp then raise R_trfs_exn2 else ()
  val emit = fn X => ( inc No_emitted_by_R; 
    stop_timer R_timer; emit X; start_timer R_timer )
  val Data = F.new( cmp, Constants.Total_max_REQ_storage )
  fun emit_from_queue( _ : real, Record, Cost_limit_opts ) =
    let
      val ( New_D, CSE_records ) = apply_R_record( R_lib2.cse, D, Record )
(* 
      val () = (
        p"\nR_trfs_with_no_of_cases_distribution: emit_from_queue:\n";
        p"\nNew_D = \n"; Print.print_dec' New_D;
       nl(); print_R_record Record;
       nl() )
*)
    in
      emit( New_D, [ R( Record, CSE_records ) ], Cost_limit_opts )
    end
  val emit_to_queue = 
    fn X as ( New_D : dec, Record, 
              Cost_limit_opts :  real option list )  =>
    case F.insert( Exp_synt.Synt_lib.Evaluate.syntactic_fingerprint New_D,
                   ( synted_syntactic_complexity( D, Record ),
                     Record,
                     Cost_limit_opts ), 
                   Data ) 
    of
      NONE => ()
    | SOME X => emit_from_queue X

  val _ = ( Sum_of_R_cost_limits := 
    !Sum_of_R_cost_limits + max( op<, Cost_limits ) )
  val () = report "Before produce_bottom_posess_list "
  val Alts : pos list list = 
    case Alts_opt of SOME Alts => Alts | NONE => filter( top_pos_ok,
      [ [] ] ::
      map( fn [ Alt ] => Alt, 
        produce_bottom_posess_list( exp, [], 1, 
          0.2 * max( op<, Cost_limits ) * 
            Exp_synt.Synt_lib.synt_and_eval_time_per_exp(),
          Exp_synt.Synt_lib.approximate_synt_time_per_exp()  ) ) )

  val () = report "Before common_scope_check "
  val Alts = filter( fn [ _ ] => true | Poses as P::_::_ =>
    common_scope_check( 
      pos_to_sub( exp, P ),
      pos_to_sub( exp, longest_common_prefix Poses ) ),
    Alts )

  val () = report "Before rconst_split "
  val { rconst_cost_limits, other_cost_limits, rconst_alts, other_alts,
        rconst_post_adjust, other_post_adjust } =
   Rconst.rconst_split( D, Cost_limits, Alts, poses_ok, Min_once )

  val () = report "After rconst_split "
  val Alts = other_alts
  val Cost_limits = other_cost_limits

  val R_top_poses_list = alt_list_to_r_top_poses_list( D, Alts ) 
  val _ = 
    if real_eq( 1.0, real_sum( map( #2, R_kind_weights ) ) ) then
      ()
    else
      raise R_trfs_exn1

  (* val Spike_table = NN_lib.make_spike_table( #exp D ) *)
  exception Spike_table_not_used_exn
  val Spike_table : int Pos_hash.hash_table =
    Pos_hash.mkTable( 0, Spike_table_not_used_exn )

  fun emit_cost_limits( post_adjust, Kind, Cost_limits ) =
  let
    val Counts = map( fn _ => ref 0, Cost_limits )
    fun emit'( D, Trf_history, Cost_opts ) = (
      loop( fn( Cost_opt, Count ) =>
        case Cost_opt of SOME _ => inc Count | NONE => (),
        combine( Cost_opts, Counts ) );
      emit_to_queue( D, Trf_history, 
        other_post_adjust( post_adjust Cost_opts ) ) )
(*
    fun emit_nn( D, Trf_history, Cost_opts ) =
    let
      val D_opt = R_lib.nn_post_opt( D, 
        real Constants.Number_of_nn_post_opt_epochs, Trf_history )
    in
    case D_opt of
      NONE => ()
    | SOME D =>
      emit_to_queue( D, Trf_history,
        other_post_adjust( post_adjust(
          map( fn NONE => NONE | SOME Cost => 
              SOME( Cost * real Constants.Number_of_nn_post_opt_epochs ), 
            Cost_opts ) ) ) )
     end
*)

    fun do_with( NN_opt, Cost_limits, emit ) =
      do_with_R_kind( Synt_and_eval_time_per_exp,
        No_of_cases_distribution, NN_opt, Kind, D, Cost_limits, 
        R_top_poses_list, Spike_table,
        poses_ok, Min_once, Eq_check, emit );
  in
    report "Before do_with true ";
(*
    if exists( fn Cost_limit => Cost_limit > 400.0, Cost_limits ) andalso
       NN_lib.is_nn( #exp D  )
    then
      do_with( true, 
        map( fn Cost_limit => 
          Cost_limit / 2.0 / real Constants.Number_of_nn_post_opt_epochs, 
          Cost_limits ), 
        emit_nn )
    else
      ();
*)
    report "Before do_with false ";
    do_with( false, Cost_limits, emit' );
    report "After do_with false ";
    map( fn( Count, Cost_limit ) => real( !Count ) / Cost_limit,
      combine( Counts, Cost_limits ) )
  end
in
  (* Modification of rconsts: *)
  Rconst.rconst_trfs( D, rconst_alts, rconst_cost_limits, 
    fn( D, Records, Cost_opts ) => 
      emit( D, Records, rconst_post_adjust Cost_opts ) );

  report "After rconst_trfs ";

  (* Identity transformation: *)
  if null Min_once andalso exists( fn L => L > 200.0, Cost_limits ) then
    emit( D,
      [ R( { r_top_poses = ( [], NONE ), bottom_poses = [], 
             bottom_labels = [], synted_exp = Dummy_exp,
             not_activated_syms = [] },
           [] ) ],
      map( fn Cost_limit =>
        if Cost_limit > 200.0 then
          SOME 200.0
        else
          NONE,
        Cost_limits ) )
  else
    ();
  adjust_cost_limits( 
    emit_cost_limits, 
    map( #1, R_kind_weights ),
    map( fn Cost_limit => 
      ( Cost_limit, map( #2, R_kind_weights ) ), 
      Cost_limits ) );
  loop( emit_from_queue, F.contents Data );
  stop_timer R_timer
(*  p"\nR_trfs finished\n"; flush_out( !std_out ) *)
end (* R_trfs *)
handle Ex => (
  p"\n\nR_trfs:\n";
  p"  D = \n"; Print.print_dec' D; nl();
  p"  Cost_limits = "; print_real_list Cost_limits; nl();
  p"  Min_once = "; print_list( fn Xs => 
    print_list( fn Sym => p( symbol_to_string Sym ), Xs ),
    Min_once ); nl();
  p"  Eq_check = "; p( Bool.toString Eq_check );
  nl();
  re_raise( Ex, "R_trfs" ) )

fun R_trfs( 
      Synt_and_eval_time_per_exp : real,
      D : dec, 
      Alts_opt : pos list list option,
      Cost_limits : real list,
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool, 
      Min_once : symbol list list, Eq_check : bool,
      emit : dec * atomic_trf_record list * real option list -> unit ) : unit =
  R_trfs_with_no_of_cases_distribution( 
    Synt_and_eval_time_per_exp,
    Constants.Default_no_of_cases_distribution,
    D, Alts_opt, Cost_limits, top_pos_ok, poses_ok, Min_once, Eq_check, emit )


end (* functor R_fn *)
