(*
  File: req_lib2.sml.
  Created: 1998-07-07.
  Modified: 1999-08-08.
*)

functor REQ_lib2_fn( Exp_synt : EXP_SYNT ) :
sig

type req_node
type make_merged_cum_map_range

val print_req_node : req_node -> unit

val first_run : real *
  REQ_lib.req_match_error_data *
  Ast.dec *
  real *
  ( Ast_lib.pos list -> bool ) *
  ( ( Ast_lib.pos * Ast_lib.pos list ) list -> bool ) *
  Ast.symbol list list *
  real
  ->
  ( make_merged_cum_map_range * ( req_node * int ) list ) option * 
  req_node list *
  ( Ast.dec -> bool )

(* The option is NONE iff no second run should be performed. *)

val second_run : real *
  REQ_lib.req_match_error_data *
  Ast.dec *
  real *
  ( Ast_lib.pos list -> bool ) *
  ( ( Ast_lib.pos * Ast_lib.pos list ) list -> bool ) *
  Ast.symbol list list *
  make_merged_cum_map_range * req_node list *
  ( { order_no : int, req_node : req_node } -> unit )
  ->
  unit

structure R : R_sig

val is_bad_time : unit -> real
(* val is_bad : Ast.dec * Ast.dec * Ast_lib2.simple_R_record list -> bool *)

val is_REQ_time : unit -> real
val is_REQ_eval_time : unit -> real
val map_time : unit -> real
val print_req_match_error_statistics : unit -> unit
end =
struct

structure R = R_fn( Exp_synt )

open Exp_synt.Synt_lib.Evaluate REQ_lib


structure BoolVector =
(* Built-in structure should be used but is not available in SML/NJ 109.11. *)
struct
  
type vector = CharVector.vector

fun from_char #"f" = false
  | from_char #"t" = true

fun to_char false = #"f"
  | to_char true = #"t"

fun fromList( Xs : bool list ) = CharVector.fromList( List1.map( to_char, Xs ) )

fun sub( Xs : vector, I : int ) : bool =
  from_char( CharVector.sub( Xs, I ) )

fun print( Xs : vector ) = (
  Lib.nl();
  CharVector.app (fn #"f" => Lib.p"0" | #"t" => Lib.p"1") Xs;
  Lib.nl() )


end (* structure BoolVector *)


type eval_type = { 
  is_REQ : BoolVector.vector,
  is_bad : bool, 
  no_pat_occ : bool, (* Is true iff there is a case-pat in the synted exp such 
                     that no var in the case-pat occurs in the synted exp. *)
  synted_syntactic_complexity : real,
  eval_value : eval_value_type
  }

fun syntactic_fingerprint( { eval_value, ... } : eval_type ) = 
  #syntactic_fingerprint eval_value

structure Map_arg =
  struct
    val Version = "req_lib2.sml"
    type eval_type = eval_type

    val truncate_syntactic_complexities = fn( { is_REQ, is_bad, no_pat_occ,
          synted_syntactic_complexity,  eval_value } : eval_type )  
        : eval_type => { 
      is_REQ = is_REQ,
      is_bad = is_bad,
      no_pat_occ = no_pat_occ,
      synted_syntactic_complexity = 
        real( Real.trunc synted_syntactic_complexity ),
      eval_value = truncate_syntactic_complexities eval_value
      }

    fun print_eval( 
          { eval_value, synted_syntactic_complexity, 
            is_REQ, is_bad, no_pat_occ, ... } : eval_type ) = (
      print_eval_value eval_value; 
      Lib.p( "   " ^ Real.toString synted_syntactic_complexity );
      BoolVector.print is_REQ;
      Lib.p( "   " ^ Bool.toString is_bad );
      Lib.p( "   " ^ Bool.toString no_pat_occ ^ "\n")
      )
    
    val syntactic_fingerprint = syntactic_fingerprint

    type REQ_record = Ast_lib2.REQ_record list
(* List used to also include records from match error handling. *)

    val Dummy_REQ_record = []

    val Max_REQ_storage = 
      Constants.Total_max_REQ_storage div 48 div length Spec.Grade.comparisons
    val _ = Lib.p("\n\nMax_REQ_storage = " ^ Int.toString Max_REQ_storage )
  end (* structure Map_arg *)

structure Map = Map( Map_arg )
    
val map_time = Map.map_time

open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib6 Print R R.R_lib Map 

val Is_REQ_timer = mk_timer "Is_REQ_timer"

fun is_REQ_time() = check_timer Is_REQ_timer

val Is_REQ_eval_time = ref 0.0
fun is_REQ_eval_time() = !Is_REQ_eval_time

val mk_eval_value = fn( X : dec ) =>
  let
    val _ = start_timer Is_REQ_timer
    val Start = cum_eval_time()
    val () = Exp_synt.Synt_lib.type_check_dec_raise X
    val Y = mk_eval_value X
  in
    Is_REQ_eval_time := ( !Is_REQ_eval_time ) + cum_eval_time() - Start;
    stop_timer Is_REQ_timer;
    Y
  end



structure Bad :
sig
  val is_bad_time : unit -> real
  val is_bad : dec * dec * simple_R_record list -> bool
  val match_error_is_bad : dec * simple_R_record -> bool
end =
struct
local


fun prohibited_exps Pat =
  let val As_subs = exp_filter(fn as_exp{...} => true | _ => false, Pat)
  in
    map(fn as_exp{pat,...} => remove_as pat, As_subs)
  end
  
fun prohibited( 
      So_far : ( 'a, 'b )e list, 
      Current_pos : pos, 
      E : ( 'a, 'b )e 
      ) : pos list =
  ( if member'( exp_eq, E, So_far ) then [ Current_pos ] else [] ) @ (
  case E of
    app_exp{ args, ... } =>
      flat_map( fn( Sub, No ) => 
        prohibited( So_far, Current_pos @ [ No ], Sub ),
        combine( args, fromto( 0, length args - 1 ) ) )
  | case_exp{ exp, rules, ... } =>
      prohibited( So_far, Current_pos @ [ 0 ], exp ) @
      flat_map( fn( { pat, exp = RHS, ... }, No ) =>
        prohibited(
          (if is_variable_exp exp then 
             remove_as pat 
           else 
             exp) ::
          prohibited_exps pat @ So_far,
          Current_pos @ [ No ],
          RHS ),
        combine( rules, fromto( 1, length rules ) ) )
  | let_exp{ dec_list, exp, ... } =>
      flat_map( fn( { pat, exp, ... }, No ) =>
        prohibited( 
          prohibited_exps pat @ So_far, 
          Current_pos @ [ No ],
          exp ),
        combine( dec_list, fromto( 0, length dec_list - 1 ) ) ) @
      prohibited( So_far, Current_pos @ [ length dec_list ], exp )
  )
    
      
in (* local *)

fun prohibited_dec( D as { pat, exp, ... } : ( 'a, 'b )d ) : pos list =
  prohibited( prohibited_exps pat, [], exp )

end (* local *)

fun is_violation Sub = not( Exp_synt.equivalence_check Sub )

exception All_records_should_be_from_the_same_R_exn

fun is_bad( 
      D, 
      New_D,
      Records as
      ( { top_pos, rel_bottom_poses, synted_exp, synted_exp_bottom_poses } :: 
        _ ) : simple_R_record list
      ) : bool =
(* All records in Records should come from one and the same R. *)
if exists( fn Record => 
     synted_exp_bottom_poses <> #synted_exp_bottom_poses Record,
     tl Records )
then
  raise All_records_should_be_from_the_same_R_exn
else
let
  val Top_poses = map( #top_pos, Records )
  val Root_top_pos = longest_common_prefix Top_poses

  (* Employed to determine if a given violation is in the old exp: *)
  val New_bottom_poses =
    flat_map( fn Top_pos =>
      map( fn P => Top_pos @ P, synted_exp_bottom_poses ),
      Top_poses )
  fun is_old Pos =
    exists( fn P => is_prefix( P, Pos ), New_bottom_poses )

  fun synted_violation Pos =
    not( is_old Pos ) andalso
    exists( fn Top_pos => is_prefix( Top_pos, Pos ), Top_poses )
  
  val Subst = pos_to_pat_subst( false, false, New_D, Root_top_pos )
  
  val E = pos_replace( #exp D, Root_top_pos,
    fn Sub => apply_exp_subst( Sub, Subst ) )

  val New_E = pos_replace( #exp New_D, Root_top_pos,
      fn Sub => apply_exp_subst( Sub, Subst ) )


  val Vs = all_poses_filter( is_violation, E )
  val New_Vs = all_poses_filter( is_violation, New_E )

in
  exists( synted_violation, New_Vs ) orelse
  not( is_subsequence( 
    filter( not o is_old, New_Vs ),
    Vs ) ) orelse
let
  val E  = #exp D
  val New_E = #exp New_D

  val Vs = all_poses_filter( is_violation, E )
  val New_Vs = all_poses_filter( is_violation, New_E )
  
  val Ps = prohibited_dec D
  val New_Ps = prohibited_dec New_D

in
(*
  p"\n Ps = "; print_pos_list Ps;
  p"\n New_Ps = "; print_pos_list New_Ps;
  nl();
*)
  exists( synted_violation, New_Vs ) orelse
  not( is_subsequence( 
    filter( not o is_old, New_Vs ),
    Vs ) ) orelse
  exists( synted_violation, New_Ps ) orelse
  not( is_subsequence( 
    filter( not o is_old, New_Ps ),
    Ps ) )
end  
end (* fun is_bad *)
handle Ex => (
  p"\n\n:is_bad:\n";
  p"\nD =\n"; Print.print_dec' D; nl();
  p"\nRecords =\n"; print_simple_R_record_list Records; nl();
  p"\nNew_D =\n"; Print.print_dec' New_D;
  raise Ex
  )

fun match_error_is_bad( New_D, 
      Simple as { top_pos, synted_exp, ... } : simple_R_record ) : bool = (
  not( null( exp_filter( is_violation, synted_exp ) ) ) orelse
  exists( fn P => is_prefix( top_pos, P ), prohibited_dec New_D ) )
handle Ex => (
  p"\n\n:match_error_is_bad:\n";
  p"\nNew_D =\n"; Print.print_dec' New_D;
  p"\nSimple =\n"; print_simple_R_record Simple; nl();
  raise Ex
  )


val T = mk_timer "is_bad_time"
fun is_bad_time() = check_timer T

val is_bad = fn X => 
  let
    val _ = start_timer T
    val Y = is_bad X
  in
    stop_timer T;
    Y
  end

end (* structure Bad *)
     
val is_bad = Bad.is_bad
val match_error_is_bad = Bad.match_error_is_bad

val is_bad_time = Bad.is_bad_time

val Pe_cmps = flat_map( fn Pei_cmp => map( fn Cmp =>
        fn(X,Y) => Pei_cmp(Cmp,X,Y), Spec.Grade.comparisons ),
      [pe1_cmp,pe2_cmp,pe3_cmp] )
(* Note that this code parallels the one for Pe_diff_cmps below. *)


fun better_or_equal( X : eval_value_type, Y ) : bool =
  exists( fn pe_cmp =>
    case pe_cmp( X, Y ) of
      LESS => true
    | EQUAL => true
    | GREATER => false,
    Pe_cmps )

fun mk_eval_value_and_match_errors( D : dec ) : eval_value_type * symbol list =
  case program_eval_fun D of PE =>
    ( program_eval_to_eval_value( D, PE ),
      make_set( filter( fn Sym => 
        is_not_activated_sym Sym andalso 
        Sym <> PREDEFINED_NOT_ACTIVATED_SYMBOL, 
        #match_errors  PE ) ) )


fun emit_from_find_REQs( D, Old_eval_value, New_D, Eval_value, 
      Match_error_records : simple_R_record list, REQ_records as _::_, emit ) =
let
  val Is_REQ = map( fn pe_cmp =>
    case pe_cmp( Eval_value, Old_eval_value ) of
      LESS => true | EQUAL => true | GREATER => false,
    Pe_cmps )
in
  if not( member( true, Is_REQ ) ) then
    ()
  else
    emit( {
      eval_value = Eval_value,
      is_REQ = BoolVector.fromList Is_REQ,
      is_bad = Bad.is_bad( D, New_D, from_REQ_record( hd REQ_records ) ) orelse
        exists( fn Simple => match_error_is_bad( New_D, Simple ), 
          Match_error_records ),
      no_pat_occ = exists( fn { synted_exp, ... } =>
        exp_count( not o pat_occ_check, synted_exp ) > 0,
        REQ_records ),
      synted_syntactic_complexity = real_sum( map( fn REQ_record =>
        synted_syntactic_complexity( D, REQ_record ),
        REQ_records ) )
      },
      REQ_records )
end (* fun emit_from_find_REQs *)


val Match_error_cost_limit_sum = ref 0.0
val Match_error_count = ref 0.0
val REQ_cost_limit_sum = ref 0.0

local

fun p S = output( !std_err, S )

in

fun print_req_match_error_statistics() = (
  p"\n\nREQ match error count = "; p( Real.toString( !Match_error_count ) );
  p"\nREQ match error cost limit sum = "; 
    p( Real.toString( !Match_error_cost_limit_sum ) );
  p"\nREQ_cost_limit_sum = "; p( Real.toString( !REQ_cost_limit_sum ) );
  p"\n" )

end (* local *)

exception Handle_match_errors_exn

fun handle_match_errors(
  Synt_and_eval_time_per_exp,
  First_call : bool, First_run : bool,
  REQ_match_error_data : req_match_error_data,
  REQ_cost_limit,
  Cost_limit : real,
  Match_errors : symbol list,
  D : dec, Old_eval_value, New_D : dec, top_pos_ok : pos list -> bool,
  Eq_check : bool, Match_error_records : simple_R_record list,
  REQ_records : REQ_record list,
  emit : Map.req_node -> unit
  ) : unit =
  case Match_errors of
    [] => ()
  | Sym :: Syms =>
  let
    val [ Top_pos ] = absolutely_all_poses_filter(
      fn app_exp{ func, ... } => func = Sym
       | _ => false,
      #exp New_D)

    val Old_top_pos_opt = 
      case absolutely_all_poses_filter(
             fn app_exp{ func, ... } => func = Sym
              | _ => false,
             #exp D)
      of
        [] => NONE
      | [ Old_top_pos ] => SOME Old_top_pos

  in
    if is_NONE Old_top_pos_opt orelse not( top_pos_ok[ Top_pos ] ) then
      handle_match_errors( Synt_and_eval_time_per_exp,
        First_call, First_run, REQ_match_error_data, 
        REQ_cost_limit, Cost_limit, Syms, D, Old_eval_value,
        New_D, top_pos_ok, Eq_check, Match_error_records, REQ_records, emit )
    else
    case Old_top_pos_opt of SOME Old_top_pos =>
  let
    val Match_error_cost_limit =
      match_error_update_and_estimate( REQ_match_error_data,
        First_call, First_run, REQ_cost_limit, Cost_limit )
(*    
    val () = (
      p"\n\nhandle_match_errors:";
      p"\nNew_D = "; Print.print_dec' New_D; nl();
      loop( print_REQ_record, REQ_records );
      p"\nMatch_error_cost_limit = "; 
        print_real Match_error_cost_limit; nl()
      )
*)
  in
    if Match_error_cost_limit < 2.0 then () else
  let
    val K = REQ_lib.K_bis( Match_error_cost_limit, 1 )

    fun emit_dec( New_D, Cost, Not_act_syms, { synted_exp, bottom_labels } ) = 
      if is_q_exp synted_exp then () else
      let
        val REQ_records =
          snoc( REQ_records, { 
            r_top_poses = ( [ Old_top_pos ], NONE ),
            bottom_poses = [],
            bottom_labels = [],
            synted_exp = synted_exp, 
            not_activated_syms = Not_act_syms
            } )

        val Match_error_records = {
          top_pos = Top_pos,
          rel_bottom_poses = [],
          synted_exp = synted_exp,
          synted_exp_bottom_poses = []
          } :: Match_error_records 

        val ( Eval_value, Match_errors ) =
          mk_eval_value_and_match_errors New_D

        val Cost = max2( op<, 2.0, K * ( Cost + real REQ_lib.Offset ) )

      in
        emit_from_find_REQs( D, Old_eval_value, New_D, Eval_value, 
          Match_error_records, REQ_records, emit );
        handle_match_errors( Synt_and_eval_time_per_exp,
        false, First_run, REQ_match_error_data, 
        REQ_cost_limit, Cost_limit / Cost, 
        make_set( Syms @ Match_errors ), D, Old_eval_value, New_D, 
        top_pos_ok, Eq_check, Match_error_records, REQ_records, emit )
      end
  in
    Match_error_cost_limit_sum := !Match_error_cost_limit_sum +
      Match_error_cost_limit;
    real_inc Match_error_count;
    R.R_lib.replace( Synt_and_eval_time_per_exp,
      Constants.Default_no_of_cases_distribution, false,
      [], [], New_D, Top_pos, [], 
      Match_error_cost_limit, nil, Eq_check, emit_dec )
  end
  end
  end (* handle_match_errors *)


fun find_REQs( Synt_and_eval_time_per_exp,
      First_run : bool,
      REQ_match_error_data : req_match_error_data,
      D : dec, 
      REQ_cost_limit : real, 
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool,
      Min_once : symbol list list,
      Eq_check : bool,
      emit : Map.req_node -> unit
      ) : unit =
let
  val Old_eval_value = mk_eval_value D

  fun emit_R( New_D, 
        [ R( REQ_record as { r_top_poses = ( Alt, _ ), synted_exp, ...  }, 
             _ ) ],
        [ Cost_opt :  real option ] ) : unit = 
    if null Alt then (* Sentinel meaning identity R. *) () else
  let
    val ( Eval_value, Match_errors ) = mk_eval_value_and_match_errors New_D
    val Cost_limit' =
      case Cost_opt of NONE => 0.0 | SOME Cost => REQ_cost_limit / Cost
  in
    emit_from_find_REQs( D, Old_eval_value, New_D, Eval_value, 
      [], [ REQ_record ], emit );
    
    handle_match_errors( Synt_and_eval_time_per_exp,
    true, First_run, REQ_match_error_data, 
    REQ_cost_limit, Cost_limit', Match_errors, D, Old_eval_value, New_D, 
    top_pos_ok, Eq_check, [], [ REQ_record ], emit )
  end
    handle Ex => (
    p"\n\nemit_R in find_REQs:";
    p"\nNew_D = "; Print.print_dec' New_D;
    p"\nREQ_record = \n"; print_REQ_record REQ_record;
    p"\n\nD = "; Print.print_dec' D;
    p("\nREQ_cost_limit = " ^ Real.toString REQ_cost_limit );
    p("\nEq_check = " ^ Bool.toString Eq_check );
    raise Ex
    )

in
  REQ_cost_limit_sum := !REQ_cost_limit_sum + REQ_cost_limit;
  REQ_lib.update_req_cost_limit_sum( REQ_match_error_data,
    true, First_run, REQ_cost_limit );
  R_trfs( Synt_and_eval_time_per_exp,
    D, NONE, [ REQ_cost_limit ], top_pos_ok, poses_ok, Min_once, 
    Eq_check, emit_R )
end (* fun find_REQs *)


structure Make_maps :
  sig
    val weighted_maps :  unit -> ( real * map_data ) list 
  end =
struct


local

open Spec

fun grade_diff_cmp( cmp : Grade.grade * Grade.grade -> order,
      L1, U1, L2, U2 ) =
let
  fun less( X, Y ) = 
    case cmp( X, Y ) of LESS => true | _ => false
  val L1' = min2( less, L1, U1 )
  val U1' = max2( less, L1, U1 )
  val L2' = min2( less, L2, U2 )
  val U2' = max2( less, L2, U2 )
in
  cmp( Grade.+( U1', L2' ), Grade.+( U2', L1' ) )
end


fun real_list_abs_diff( [], [] ) = []
  | real_list_abs_diff( X::Xs, Y::Ys ) = 
      Real.abs( X - Y ) :: real_list_abs_diff( Xs, Ys )

fun diff_cmp( cmp, pei_listing, 
      { lower1, upper1, lower2, upper2 } ) =
let
  val ( Ls1, L1, Ls1' ) = pei_listing lower1
  val ( Us1, U1, Us1' ) = pei_listing upper1
  val ( Ls2, L2, Ls2' ) = pei_listing lower2
  val ( Us2, U2, Us2' ) = pei_listing upper2
in
  case list_compare( Real.compare,
         real_list_abs_diff( Ls1, Us1 ),
         real_list_abs_diff( Ls2, Us2 ) )
  of
    EQUAL => (
      case grade_diff_cmp( cmp, L1, U1, L2, U2 ) of
        EQUAL => 
          list_compare( Real.compare,
            real_list_abs_diff( Ls1', Us1' ),
            real_list_abs_diff( Ls2', Us2' ) )
      | X => X 
      )
  | X => X
end

val Pe_diff_cmps = map( fn pei_listing =>
  fn( cmp, X ) => diff_cmp( cmp, pei_listing, X ),
  [ pe1_listing, pe2_listing, pe3_listing ] )

in (* local *)

val Pe_diff_cmps = flat_map( fn pei_diff_cmp => map( fn cmp =>
  fn X => pei_diff_cmp( cmp, X ), Grade.comparisons ),
  Pe_diff_cmps )
(* Note that this code parallels the one for Pe_cmps above. *)

end (* local *)


val Pe_cmps = map( fn pe_cmp =>
  fn( X : eval_type,  Y : eval_type ) => 
    pe_cmp( #eval_value X, #eval_value Y ),
  Pe_cmps )

val Pe_diff_cmps = map( fn pe_diff_cmp =>
  fn{ lower1 : eval_type, upper1 : eval_type,
      lower2 : eval_type, upper2 : eval_type } =>
    pe_diff_cmp{
      lower1 = #eval_value lower1,
      upper1 = #eval_value upper1,
      lower2 = #eval_value lower2,
      upper2 = #eval_value upper2 },
  Pe_diff_cmps )





fun bad_cmp'( Is_bad1 : bool, Is_bad2 : bool ) : order =
  case ( Is_bad1, Is_bad2 ) of
    ( false, false ) => EQUAL
  | ( true, true ) => EQUAL
  | ( false, true ) => (* Good, Bad *) LESS
  | ( true, false ) => (* Bad, Good *) GREATER

val bad_cmp = fn( X : eval_type, Y : eval_type ) =>
  bad_cmp'( #is_bad X, #is_bad Y )

val no_pat_occ_cmp = fn( X : eval_type, Y : eval_type ) =>
  bad_cmp'( #no_pat_occ X, #no_pat_occ Y )



fun bad_diff_cmp{ lower1 : eval_type, upper1 : eval_type,
      lower2 : eval_type, upper2 : eval_type } =
  case ( #is_bad lower1 = #is_bad upper1, #is_bad lower2 = #is_bad upper2 ) of
    ( false, false ) => EQUAL
  | ( false, true ) => GREATER
  | ( true, false ) => LESS
  | ( true, true ) => EQUAL


fun no_pat_occ_diff_cmp{ lower1 : eval_type, upper1 : eval_type,
      lower2 : eval_type, upper2 : eval_type } =
  case ( #no_pat_occ lower1 = #no_pat_occ upper1, 
         #no_pat_occ lower2 = #no_pat_occ upper2 ) of
    ( false, false ) => EQUAL
  | ( false, true ) => GREATER
  | ( true, false ) => LESS
  | ( true, true ) => EQUAL


fun synted_compl_cmp( X : eval_type, Y : eval_type ) =
  real_compare(
    #synted_syntactic_complexity X,
    #synted_syntactic_complexity Y)


fun main_compl_cmp( X : eval_type, Y : eval_type ) =
  real_compare(
    main_syntactic_complexity( #eval_value X ),
    main_syntactic_complexity( #eval_value Y ) )


fun synted_compl_diff_cmp{ lower1 : eval_type, upper1 : eval_type,
      lower2 : eval_type, upper2 : eval_type } =
let
  fun s( X : eval_type ) = #synted_syntactic_complexity X
in
  real_compare(
    Real.abs( s lower1 - s upper1 ),
    Real.abs( s lower2 - s upper2 ) )
end


fun main_compl_diff_cmp{ lower1 : eval_type, upper1 : eval_type,
      lower2 : eval_type, upper2 : eval_type } =
let
  fun s( X : eval_type ) = main_syntactic_complexity( #eval_value X )
in
  real_compare(
    Real.abs( s lower1 - s upper1 ),
    Real.abs( s lower2 - s upper2 ) )
end



fun compose_cmps( cmp1, cmp2 ) =
  fn X =>
    case cmp1 X of
      EQUAL => cmp2 X
    | Y => Y

val synted_compl_cmp = compose_cmps( synted_compl_cmp, main_compl_cmp )
val main_compl_cmp = compose_cmps( main_compl_cmp, synted_compl_cmp )


val synted_compl_diff_cmp = 
  compose_cmps( synted_compl_diff_cmp, main_compl_diff_cmp )
val main_compl_diff_cmp = 
  compose_cmps( main_compl_diff_cmp, synted_compl_diff_cmp )

local

val Numbered_cmps = flat_map( fn ( pe_cmp, No ) => 
  flat_map( fn compl_cmp =>
    [ ( compose_cmps( pe_cmp, compl_cmp ), No ),
      ( compose_cmps( compl_cmp, pe_cmp ), No )
      ],
  [ synted_compl_cmp, main_compl_cmp ] ),
    indexize( Pe_cmps, 0 ) )

in

val Cmps = map( fn( cmp, No ) =>
  fn( X : eval_type, Y : eval_type ) =>
  case ( BoolVector.sub( #is_REQ X, No ), BoolVector.sub( #is_REQ Y, No ) ) of
    ( false, false ) => cmp( X, Y )
  | ( false, true ) => GREATER
  | ( true, false ) => LESS
  | ( true, true ) => cmp( X, Y ),
  Numbered_cmps )

end (* local *)



local

val Pat_occ_cmps = map( fn cmp => compose_cmps( no_pat_occ_cmp, cmp ), Cmps )
val No_pat_occ_cmps = map( fn cmp => compose_cmps( cmp, no_pat_occ_cmp ), Cmps )

in

val Good_pat_occ_cmps = 
  map( fn cmp => compose_cmps( bad_cmp, cmp ), Pat_occ_cmps )

val Bad_pat_occ_cmps = 
  map( fn cmp => compose_cmps( cmp, bad_cmp ), Pat_occ_cmps )


val Good_no_pat_occ_cmps = 
  map( fn cmp => compose_cmps( bad_cmp, cmp ), No_pat_occ_cmps )

val Bad_no_pat_occ_cmps = 
  map( fn cmp => compose_cmps( cmp, bad_cmp ), No_pat_occ_cmps )

end (* local *)

local

val Numbered_diff_cmps = flat_map( fn( pe_diff_cmp, No ) => 
  flat_map( fn compl_diff_cmp =>
    [ ( compose_cmps( pe_diff_cmp, compl_diff_cmp ), No ),
      ( compose_cmps( compl_diff_cmp, pe_diff_cmp ), No )
      ],
  [ synted_compl_diff_cmp, main_compl_diff_cmp ] ),
    indexize( Pe_diff_cmps, 0 ) )

in

val Diff_cmps = map( fn( diff_cmp, No ) =>
  let
    fun is_REQ( X : eval_type ) = BoolVector.sub( #is_REQ X, No )
  in
  fn Arg as { lower1, upper1, lower2, upper2 } =>
  case ( is_REQ lower1 = is_REQ upper1, is_REQ lower2 = is_REQ upper2 ) of
    ( false, false ) => diff_cmp Arg
  | ( false, true ) => GREATER
  | ( true, false ) => LESS
  | ( true, true ) => diff_cmp Arg
  end,
  Numbered_diff_cmps )
  
end (* local *)



local

val Pat_occ_diff_cmps = map( fn diff_cmp => 
  compose_cmps( no_pat_occ_diff_cmp, diff_cmp ), Diff_cmps )

val No_pat_occ_diff_cmps = map( fn diff_cmp => 
  compose_cmps( diff_cmp, no_pat_occ_diff_cmp ), Diff_cmps )

in

val Good_pat_occ_diff_cmps = map( fn diff_cmp => 
  compose_cmps( bad_diff_cmp, diff_cmp ), Pat_occ_diff_cmps )

val Bad_pat_occ_diff_cmps = map( fn diff_cmp => 
  compose_cmps( diff_cmp, bad_diff_cmp), Pat_occ_diff_cmps )


val Good_no_pat_occ_diff_cmps = map( fn diff_cmp => 
  compose_cmps( bad_diff_cmp, diff_cmp ), No_pat_occ_diff_cmps )

val Bad_no_pat_occ_diff_cmps = map( fn diff_cmp => 
  compose_cmps( diff_cmp, bad_diff_cmp), No_pat_occ_diff_cmps )

end (* local *)



exception Make_maps_exn

val N = length Good_pat_occ_cmps

val _ = 
  if N = length Good_no_pat_occ_cmps andalso 
     N = length Bad_pat_occ_cmps andalso
     N = length Bad_no_pat_occ_cmps andalso 

     N = length Good_pat_occ_diff_cmps andalso 
     N = length Good_no_pat_occ_diff_cmps andalso 
     N = length Bad_pat_occ_diff_cmps andalso
     N = length Bad_no_pat_occ_diff_cmps
  then
    ()
  else
    raise Make_maps_exn

exception Higher_pe1_weight_exn
fun higher_pe1_weight Cmps =
let
  val N = length Cmps
  val () = if N mod 3 <> 0 then raise Higher_pe1_weight_exn else ()
  val First = take( N div 3, Cmps )
  val Last = drop( N div 3, Cmps )
  val W1 = 0.7 / real( N div 3 )
  val W2_3 = 0.15 / real( N div 3 )
in
  map( fn Cmp => ( Cmp, W1 ),  First ) @
  map( fn Cmp => ( Cmp, W2_3 ), Last )
end
  
fun weighted_maps() = 
let

  val X::Xs =
    combine( higher_pe1_weight Good_pat_occ_cmps, Good_pat_occ_diff_cmps )
  
  val First = case X of ( ( pe_cmp, W ), pe_diff_cmp ) =>
    ( 0.70*0.60 * W, empty_map( true, pe_cmp, pe_diff_cmp ) )

  val Good_pat_occ = First :: map( fn( ( pe_cmp, W ), pe_diff_cmp ) =>
    ( 0.70*0.60 * W, empty_map( false, pe_cmp, pe_diff_cmp ) ),
    Xs )

  val Good_no_pat_occ = map( fn( ( pe_cmp, W ), pe_diff_cmp ) =>
    ( 0.70*0.40 * W, empty_map( false, pe_cmp, pe_diff_cmp ) ),
    combine( higher_pe1_weight Good_no_pat_occ_cmps, 
             Good_no_pat_occ_diff_cmps ) )

  val Bad_pat_occ = map( fn( ( pe_cmp, W ), pe_diff_cmp ) =>
    ( 0.30*0.60 * W, empty_map( false, pe_cmp, pe_diff_cmp ) ),
    combine( higher_pe1_weight Bad_pat_occ_cmps, Bad_pat_occ_diff_cmps ) )

  val Bad_no_pat_occ = map( fn( ( pe_cmp, W ), pe_diff_cmp ) =>
    ( 0.30*0.40 * W, empty_map( false, pe_cmp, pe_diff_cmp ) ),
    combine( higher_pe1_weight Bad_no_pat_occ_cmps, Bad_no_pat_occ_diff_cmps ) )

in
  Good_pat_occ @ Good_no_pat_occ @ Bad_pat_occ @ Bad_no_pat_occ
end

val _ =
  if real_eq( real_sum( map( #1, weighted_maps() ) ), 1.0 ) then
    ()
  else
    raise Make_maps_exn


end (* structure Make_maps *)


fun print_eval_type( 
      { is_bad, no_pat_occ, synted_syntactic_complexity, eval_value, ...
        } : eval_type
      ) : unit = (
  print_eval_value eval_value;
  p( "is_bad = " ^ Bool.toString is_bad );
  p( "\nno_pat_occ = " ^ Bool.toString no_pat_occ );
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

fun run( Synt_and_eval_time_per_exp,
      First_run : bool,
      REQ_match_error_data,
      D : dec, 
      REQ_cost_limit : real, 
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool,
      Min_once : symbol list list,
      emit : Map.req_node -> unit
      ) : unit = 
let
  val Data = F.new( cmp, Constants.Total_max_REQ_storage )
  val emit_to_queue = fn X => 
    case F.insert( syntactic_fingerprint( #1 X ), X, Data ) of
      NONE => ()
    | SOME X => emit X
in
  find_REQs( Synt_and_eval_time_per_exp, First_run, REQ_match_error_data, 
    D, 0.9 * REQ_cost_limit, 
    top_pos_ok, poses_ok, Min_once, true, emit_to_queue );
  find_REQs( Synt_and_eval_time_per_exp, First_run, REQ_match_error_data, 
     D, 0.1 * REQ_cost_limit, 
    top_pos_ok, poses_ok, Min_once, false, emit_to_queue );
  loop( emit, F.contents Data )
end

end (* local *)

fun first_run( Synt_and_eval_time_per_exp,
      REQ_match_error_data,
      D : dec, 
      REQ_cost_limit : real, 
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool,
      Min_once : symbol list list,
      Greatest_cost_limit : real
      ) : ( Map.make_merged_cum_map_range * ( req_node * int ) list ) option *
          Map.req_node list *
          ( dec -> bool ) =
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
  val () = 
    run( Synt_and_eval_time_per_exp, true, REQ_match_error_data, 
       D, REQ_cost_limit, top_pos_ok, poses_ok, Min_once, ins )
  val REQ_card = !REQ_card
  val MMR = Map.make_merged_cum_map( Weighted_maps, D0 )
  val REQ_PQ_prefix = Map.get_req_pq_prefix MMR
  val Reqs_and_mults = Map.get_other_reqs_and_mults MMR
  val N = length REQ_PQ_prefix
  val Needed = 
    REQ_card > Map_arg.Max_REQ_storage andalso
    REQ_lib.second_run_needed( REQ_card, N, Greatest_cost_limit )
  val Old_eval = mk_eval_value D
  fun is_REQ New_D =
    better_or_equal( mk_eval_value New_D, Old_eval )
in
  ( if Needed then SOME( MMR, Reqs_and_mults ) else NONE, 
    REQ_PQ_prefix,
    is_REQ )
end (* fun first_run *)
  

structure S = Real_set

fun second_run( Synt_and_eval_time_per_exp,
      REQ_match_error_data,
      D : dec, 
      REQ_cost_limit : real, 
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool,
      Min_once : symbol list list,
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
  run( Synt_and_eval_time_per_exp, false, REQ_match_error_data,  
    D, REQ_cost_limit, top_pos_ok, poses_ok, Min_once, emit' )
end (* fun second_run *)
  
type req_node = Map.req_node
type make_merged_cum_map_range = Map.make_merged_cum_map_range


end (* functor REQ_lib2_fn *)
