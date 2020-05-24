(* File: compound_trf_synt.sml.
   Created: 1993-07-14.
   Modified: 2000-03-20.

2000-03-20:
  Weights on start_dupl_rule and multir_r_rule changed to 5.0E3 and
  8.0E3 respectively. Now: 10.0 and 40.0.

2000-04-04:
  Rconst synt bypass for Overall_cost_limit < 9.0E3.
*)

signature COMPOUND_TRF_SYNT =
sig

structure Exp_synt : EXP_SYNT

val produce_children : real * Ast.dec * real * REQ_lib.req_match_error_data *
  ( Ast.dec * Ast_lib2.atomic_trf_record list *
   Exp_synt.Synt_lib.Evaluate.program_eval_type -> unit )
  -> real

val no_of_compound_trf_synt_evals : unit -> real
val clear_match_error_statistics : unit -> unit
val print_match_error_statistics : unit -> unit
val print_time_report : unit -> unit

val set_wanted_decs : ( string * Ast.dec ) list -> unit

end

functor Compound_trf_synt_functor( Spec : SPEC ) : COMPOUND_TRF_SYNT =
struct
open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib3 Ast_lib6 Print
structure Exp_synt = Exp_synt_functor( Spec )

val Test = false

val () = Exp_synt.initialize( Spec.Spec_file_name ) 
val _ = Exp_synt.Synt_lib.initialize_approximate_synt_time_per_exp()

structure REQ = REQ_fn( Exp_synt )
structure R = REQ.R
structure MULTIR = MULTIR_fn( R )
structure MULTIR_R = MULTIR_R_functor( R )
structure DUPL = DUPL_fn( R.R_lib )
structure Case_dist = Case_dist_functor( Exp_synt )
structure Synt_lib = Exp_synt.Synt_lib
structure Compound_trf_synt_lib = Compound_trf_synt_lib( Synt_lib )
structure Abstr = Abstr( Synt_lib )
structure Evaluate = Synt_lib.Evaluate
open R MULTIR DUPL REQ Case_dist Abstr Synt_lib Compound_trf_synt_lib

val set_wanted_decs = Compound_trf_synt_lib.set_wanted_decs

fun ABSTR_trfs( D, Cost_limits, top_pos_ok, bottom_poses_ok, emit ) =
  Abstr.ABSTR_trfs( D,
    map( fn L => { emb_coupled = false, cost_limit = L }, Cost_limits ),
    top_pos_ok, bottom_poses_ok, emit );

fun CASE_DIST_trfs( D, Cost_limits, REQ_cost_limit, top_pos_ok, emit ) =
  Case_dist.CASE_DIST_trfs( fn X => X, fn X => X, 
    D, Cost_limits, REQ_cost_limit, top_pos_ok, emit )

fun R_trfs( D, Cost_limits, _ : real, top_pos_ok, poses_ok, Min_once, emit ) =
  R.R_trfs( R.R_lib.Exp_synt.Synt_lib.synt_and_eval_time_per_exp(),
    D, NONE, Cost_limits, top_pos_ok, poses_ok, Min_once, true, emit )



(* Global variables: *)

val No_of_compound_trf_synt_evals = ref 0.0
fun no_of_compound_trf_synt_evals() = !No_of_compound_trf_synt_evals


val Match_error_count = ref 0.0
val Match_error_cost_limit_sum = ref 0.0
val Overall_cost_limit_sum = ref 0.0
val No_of_match_error_evals = ref 0.0

fun clear_match_error_statistics() = (
  Match_error_count := 0.0;
  Match_error_cost_limit_sum := 0.0
  )

local

fun p S = output( !std_err, S )

in

fun print_match_error_statistics() = (
  p("\n\nMatch_error_count = " ^ Real.toString( !Match_error_count ) );
  p("\nMatch_error_cost_limit_sum = " ^ 
   Real.toString( !Match_error_cost_limit_sum ) );

  p("\n\nOverall_cost_limit_sum = " ^ 
    Real.toString( !Overall_cost_limit_sum ) );
  p("\n\nNo_of_compound_trf_synt_evals = " ^ 
    Real.toString( !No_of_compound_trf_synt_evals ) );
  p("\n\nNo_of_match_error_evals = " ^ 
    Real.toString( !No_of_match_error_evals ) );
  p"\n\n";
  REQ.print_req_match_error_statistics();
  p"\n\n";
  flush_out( !std_err ) )

val Compound_trf_synt_timer = mk_timer "Compound_trf_synt_timer"

val () = start_timer Compound_trf_synt_timer

fun print_time_report() = (
    p("\n\nCompound trf synt global time = "^
      Real.toString(check_timer Compound_trf_synt_timer)^"\n");
    p("No of evaluations = "^Real.toString(Evaluate.no_of_evaluations())^"\n");
    p("Cumulative eval time = "^
      Real.toString(Evaluate.cum_eval_time())^"\n");
    p("Syntactic complexity time = "^
      Real.toString(Evaluate.syntactic_complexity_time())^"\n");
    p("Syntactic fingerprinting time = "^
      Real.toString(Evaluate.syntactic_fingerprint_time())^"\n");
    p("Cumulative pure exp synt time = " ^ 
      Real.toString(Exp_synt.cum_pure_exp_synt_time())^"\n");
    p("Cumulative exp synt time = " ^ 
      Real.toString(Exp_synt.cum_exp_synt_time())^"\n");
    p("Cumulative small exp synt time = " ^ 
      Real.toString(Exp_synt.cum_small_exp_synt_time())^"\n");
    p("multir_r time = " ^ 
      Real.toString( MULTIR_R.multir_r_time() )^"\n");
    p( "Map time = " ^ Real.toString( REQ.map_time() ) ^ "\n" );
    flush_out( !std_err )
)

end (* local *)

  
(* Coupling rule procedures: *)

fun req_cost_limit Global_cost_limits =
  0.7 * real_sum Global_cost_limits


fun rel_D_pos( Current_program : dec, Let_exp_pos : pos, Func : symbol )
   : dec * int =
let
  val let_exp{ dec_list, ... } = pos_to_sub( #exp Current_program, Let_exp_pos )

  val SOME Rel_D_pos = index_opt'( fn{ func, ... } => func = Func, dec_list )
in
  ( nth( dec_list, Rel_D_pos ), Rel_D_pos )
end
handle Ex => (
  p"\nrel_D_pos: Current_program =\n"; Print.print_dec' Current_program;
  p"\nrel_D_pos: Let_exp_pos = "; print_pos Let_exp_pos; nl();
  p( "\nrel_D_pos: Func = " ^ symbol_to_string Func ); nl(); nl();
  re_raise( Ex, "rel_D_pos" ) )



fun start_abstr( Current_program, nil, Local_cost_limits, emit ) =
  ABSTR_trfs( Current_program, Local_cost_limits, 
    fn _ => true, fn _ => true, fn X => emit( X, nil ) )


fun start_req( Current_program, nil, Local_cost_limits, 
  Global_cost_limits, REQ_match_error_data, emit ) =
  REQ_trfs( REQ_match_error_data, Current_program, Local_cost_limits, 
    req_cost_limit Global_cost_limits,
    fn _ => true, fn _ => true, [], fn X => emit( X, nil ) )

fun start_dupl( Current_program, nil, Local_cost_limits, 
  Global_cost_limits, _,  emit ) =
  DUPL_trfs( Current_program, Local_cost_limits, 
    0.5 * req_cost_limit Global_cost_limits,
    fn X => emit( X, nil ) )


fun start_case_dist( Current_program, nil, Local_cost_limits, 
  Global_cost_limits, _,  emit ) =
  CASE_DIST_trfs( Current_program, Local_cost_limits, 
    req_cost_limit Global_cost_limits,
    fn _ => true, fn X => emit( X, nil ) )



fun dupl_abstr( Current_program, 
  Trf_history as DUPL{ selected_rhs_poses, ... } :: _ 
  : atomic_trf_record list,
  Local_cost_limits, emit ) : unit =
let
  fun E_poses_ok E_poses = true

  fun H_pos_ok H_pos =
    exists( fn Selected => is_prefix( Selected, H_pos ), selected_rhs_poses )
in
  ABSTR_trfs( Current_program, Local_cost_limits, H_pos_ok, E_poses_ok, 
    fn X => emit( X, Trf_history ) )
end (* fun dupl_abstr *)

fun dupl_req( Current_program,
      Trf_history as DUPL{ selected_rhs_poses, ... } :: _ 
      : atomic_trf_record list,
      Local_cost_limits, 
      Global_cost_limits, REQ_match_error_data, emit ) =
let
  fun top_pos_ok Poses = forall( fn Pos =>
    exists( fn Selected => is_prefix( Selected, Pos ), selected_rhs_poses ),
    Poses )

  fun poses_ok( Tops_and_bottoms : ( pos * pos list ) list ) =
    forall( fn( Top_pos, _ ) => top_pos_ok[ Top_pos ], Tops_and_bottoms )
in
  REQ_trfs( REQ_match_error_data, Current_program, Local_cost_limits, 
    req_cost_limit Global_cost_limits,
    top_pos_ok, poses_ok, [], fn X => emit( X, Trf_history ) )
end

fun dupl_case_dist( Current_program, 
      Trf_history as DUPL{ selected_rhs_poses, ... } :: _ 
      : atomic_trf_record list,
      Local_cost_limits, Global_cost_limits, _,  emit ) : unit =
let
  fun pos_ok Pos =
    exists( fn Selected => is_prefix( Selected, Pos ), selected_rhs_poses )
in
  CASE_DIST_trfs( Current_program, Local_cost_limits,
    req_cost_limit Global_cost_limits, pos_ok, fn X => emit( X, Trf_history ) )
end

fun dupl_r' MULTIR_or_R_trfs ( Current_program, 
      Trf_history as DUPL{ selected_rhs_poses, ... } :: _ 
      : atomic_trf_record list,
      Local_cost_limits, Global_cost_limits, _, 
      emit ) : unit =
let
  fun top_pos_ok R_top_poses = forall( fn R_top_pos =>
    exists( fn Selected => is_prefix( Selected, R_top_pos ), 
            selected_rhs_poses ),
    R_top_poses )

  fun is_ok( R_top_pos, R_bottom_poses ) = top_pos_ok[ R_top_pos ]

  fun poses_ok Xss = forall( is_ok, Xss )
in
  MULTIR_or_R_trfs( Current_program, Local_cost_limits, 
    0.7 * req_cost_limit Global_cost_limits,
    top_pos_ok, poses_ok, [],
    fn X => emit( X, Trf_history ) )
end (* fun dupl_r' *)
  



local

fun update_ABSTR_record( New_program : dec,
      ABSTR{ let_exp_pos, func, parameters_added, abstr_kind }
      ) : atomic_trf_record =
  let
    fun found( let_exp{ dec_list, ... } ) =
          not( null( filter( fn{ func = F, ... } => func = F, dec_list ) ) )
      | found _ = false

    val [ Let_exp_pos ] =
      all_poses_filter( found, #exp New_program )
  in
    ABSTR{ let_exp_pos = Let_exp_pos, func = func, 
           parameters_added = parameters_added, abstr_kind = abstr_kind }
  end

in

fun abstr_req( Current_program, Trf_history, Local_cost_limits, 
      Global_cost_limits, REQ_match_error_data, emit ) =
let
  val [ ABSTR{ let_exp_pos, func, parameters_added, abstr_kind } ] =
    filter( fn ABSTR{ ... } => true | _ => false, Trf_history )

  fun top_pos_ok Poses = forall( fn Pos =>
    is_strict_prefix( let_exp_pos, Pos ),
    Poses )

  fun poses_ok( Tops_and_bottoms : ( pos * pos list ) list ) =
    forall( fn( Top_pos, _ ) => top_pos_ok[ Top_pos ], Tops_and_bottoms )

  val Min_once = [ func :: flat_map( vars_in_pat, parameters_added ) ]
(* Note that req_abstr2 can be sued instead if neither the function nor
   any of its parameters are used. *)

  val emit = fn( X as ( New_program, _, _ ), Trf_history ) =>
    emit( X,
      map( fn Record as ABSTR{ ...} => 
              update_ABSTR_record( New_program, Record )
          | Record => Record,
      Trf_history ) )
in
  REQ_trfs( REQ_match_error_data, Current_program, Local_cost_limits, 
    req_cost_limit Global_cost_limits,
    top_pos_ok, poses_ok, Min_once, fn X => emit( X, Trf_history ) )
end

end (* local *)

fun req_abstr( Current_program, 
  Trf_history as REQ( _, { after_cse, ... } ) :: _ : atomic_trf_record list,
  Local_cost_limits, emit ) : unit =
let
  
  val Top_and_bottoms_list : ( pos * pos list ) list =
    map( top_and_bottoms, after_cse )

(* At least some synted code should be inside, but not completely inside,
   some E_i. This prevents the REQ in req_abstr from being made
   redundant by the REQ in abstr_req.
*)
  fun E_pos_ok E_pos =
    exists( fn( Top_pos, Bottom_poses ) =>
      is_strict_prefix( Top_pos, E_pos ) andalso
      not( exists( fn Bottom_pos => is_prefix( Bottom_pos, E_pos ), 
             Bottom_poses ) ),
      Top_and_bottoms_list )

  fun E_poses_ok E_poses = exists( E_pos_ok, E_poses )

  fun H_pos_ok H_pos =
    exists( fn( Top_pos, _ ) => prefix_related( H_pos, Top_pos ),
      Top_and_bottoms_list )

in
  ABSTR_trfs( Current_program, Local_cost_limits, H_pos_ok, E_poses_ok, 
    fn X => emit( X, Trf_history ) )
end (* fun req_abstr *)


fun req_abstr2( Current_program, 
  Trf_history as REQ( _, { after_cse, ... } ) :: _ : atomic_trf_record list,
  Local_cost_limits, emit ) : unit =
let
  
  val Top_and_bottoms_list : ( pos * pos list ) list =
    map( top_and_bottoms, after_cse )

(* 
This rule is a more free coupling between REQ and ABSTR than req_abstr.
Advantages with REQ_ABSTR instead of ABSTR_REQ:
1. Free pos choices for 2nd, 3rd and 4th REQ.
2. Greater exp synt limit for REQ exp synt is available. ABSTR-REQ coupling
   will duplicate the same exp synt for each ABSTR if the REQ can
   be done before the ABSTR!
3. The invented function is not available which eliminates some REQs.
*)
  fun E_pos_ok E_pos =
    exists( fn( Top_pos, Bottom_poses ) =>
      is_strict_prefix( Top_pos, E_pos ) andalso
      not( exists( fn Bottom_pos => is_prefix( Bottom_pos, E_pos ), 
             Bottom_poses ) ),
      Top_and_bottoms_list )

  fun E_poses_ok E_poses = not( exists( E_pos_ok, E_poses ) )

  fun H_pos_ok H_pos =
    exists( fn( Top_pos, _ ) => prefix_related( H_pos, Top_pos ),
      Top_and_bottoms_list )

in
  ABSTR_trfs( Current_program, Local_cost_limits, H_pos_ok, E_poses_ok, 
    fn X => emit( X, Trf_history ) )
end (* fun req_abstr2 *)



fun req_case_dist( Current_program, 
  Trf_history as REQ( _, { after_cse, ... } ) :: _ : atomic_trf_record list,
  Local_cost_limits, Global_cost_limits, _, emit ) : unit =
let
  
  val Top_and_bottoms_list : ( pos * pos list ) list =
    map( top_and_bottoms, after_cse )

  (* A synted case is distributed. *)
  fun pos_ok Pos =
    exists( fn( Top_pos, Bottom_poses ) =>
      is_prefix( Top_pos, Pos ) andalso
      not( exists( fn Bottom_pos => is_prefix( Bottom_pos, Pos ), 
                   Bottom_poses ) ),
      Top_and_bottoms_list )
in
  CASE_DIST_trfs( Current_program, Local_cost_limits,
    req_cost_limit Global_cost_limits, pos_ok, fn X => emit( X, Trf_history ) )
end


local

exception update_ABSTR_record_exn1
fun update_ABSTR_record( New_program : dec,
      ABSTR{ let_exp_pos, func, parameters_added, abstr_kind },
      pos_transform : pos -> pos list
      ) : atomic_trf_record option = (
  case pos_transform let_exp_pos of
    [] => NONE
  | Pos :: _ => 
  case pos_to_sub( #exp New_program, Pos ) of
    let_exp{ dec_list = [ { func, ... } ], ... } =>
      SOME( 
        ABSTR{ let_exp_pos = Pos, func = func, 
          parameters_added = [] (* Not known *), abstr_kind = abstr_kind } )
  | E => 
      if is_not_activated_exp E then NONE else raise update_ABSTR_record_exn1
   )
  handle Ex => (
    p"\n\nupdate_ABSTR_record:\n";
    p"New_program = \n"; Print.print_dec' New_program;
    nl();
    re_raise( Ex, "update_ABSTR_record" )
    )

in


fun abstr_case_dist( Current_program, Trf_history, Local_cost_limits, 
      Global_cost_limits, _,  emit ) =
let
  val ABSTR{ let_exp_pos, func, parameters_added, abstr_kind } :: _ =
    Trf_history

  fun top_pos_ok Pos = Pos = let_exp_pos
  
  val emit = fn X as ( D, Records, Costs ) =>
    case Records of [ CASE_DIST{ pos_transform : pos -> pos list, ... } ] =>
    case update_ABSTR_record( D, hd Trf_history, pos_transform ) of
      NONE => ()
    | SOME ABSTR_record => emit( X, ABSTR_record :: tl Trf_history )

in
  CASE_DIST_trfs( Current_program, Local_cost_limits, 
    req_cost_limit Global_cost_limits,
    top_pos_ok, emit )
end

end (* local *)


fun abstr_r' MULTIR_or_R_trfs ( Current_program, Trf_history, 
      Local_cost_limits, Global_cost_limits, _,
      emit ) : unit =
let
  val [ ABSTR{ let_exp_pos, func, parameters_added, abstr_kind } ] =
    filter( fn ABSTR{ ... } => true | _ => false, Trf_history )

  val Simples : simple_R_record list =
    flat_map( fn REQ( _, { after_cse, ... } ) => after_cse | _ => [],
      takewhile( fn ABSTR{...} => false | _ => true, Trf_history ) )

  val Top_and_bottoms_list : ( pos * pos list ) list =
    map( top_and_bottoms, Simples )

  val ( D, Rel_D_pos ) = rel_D_pos( Current_program, let_exp_pos, func )

  val Min_once : symbol list list =
    case #pat D of
      app_exp{ func, args, ... } =>
        if func = TUPLE then
          map( vars_in_pat, args )
        else
          [ vars_in_pat( #pat D ) ]
    | _ =>
          [ vars_in_pat( #pat D ) ]

  val Min_once =
    filter( fn Syms =>
      not( exists( fn Sym => sym_exp_member( Sym, #exp D ), Syms ) ),
      Min_once )

  fun top_pos_ok Poses = forall( fn Pos =>
    if null Min_once then
      is_strict_prefix( let_exp_pos, Pos )
    else
      is_prefix( snoc( let_exp_pos, Rel_D_pos ), Pos ),
    Poses )

  fun is_ok( R_top_pos, R_bottom_poses ) =
    top_pos_ok [ R_top_pos ] andalso
    forall( fn( Top_pos, Bottom_poses ) =>
      not( is_prefix( R_top_pos, Top_pos ) ) orelse
      exists( fn R_bottom_pos => is_prefix( R_bottom_pos, Top_pos ), 
        R_bottom_poses ),
      Top_and_bottoms_list )

  fun poses_ok( Xss : ( pos * pos list ) list ) = forall( is_ok, Xss )

  val Let_exp as let_exp{ ... } = 
    pos_to_sub( #exp Current_program, let_exp_pos )

  val Min_once = 
    if sym_exp_count( func, Let_exp ) <= 1 then
      [ func ] :: Min_once
    else
      Min_once
in
  MULTIR_or_R_trfs( Current_program, Local_cost_limits, 
    0.7 * req_cost_limit Global_cost_limits,
    top_pos_ok, poses_ok, Min_once,
    fn X => emit( X, Trf_history ) )
end (* fun abstr_r' *)

  
fun req_r' MULTIR_or_R_trfs ( Current_program, 
  Trf_history as REQ( _, { after_cse, ... } ) :: _ : atomic_trf_record list,
  Local_cost_limits, Global_cost_limits, _, emit ) : unit =
let
  val Top_and_bottoms_list : ( pos * pos list ) list =
    map( top_and_bottoms, after_cse )
  
  fun top_pos_ok R_top_poses =
    forall( fn R_top_pos =>
      exists( fn( Top_pos, Bottom_poses ) =>
        is_prefix( Top_pos, R_top_pos ) andalso
        not( exists( fn Bottom_pos => is_prefix( Bottom_pos, R_top_pos ),
               Bottom_poses ) ),
        Top_and_bottoms_list ),
      R_top_poses )

  fun is_ok( R_top_pos, R_bottom_poses ) =
    top_pos_ok[ R_top_pos ] andalso
      exists( fn( Top_pos, Bottom_poses ) =>
        if R_top_pos = Top_pos then not( null R_bottom_poses ) else true,
        Top_and_bottoms_list )

  fun poses_ok Xss = forall( is_ok, Xss )
in
  MULTIR_or_R_trfs( Current_program, Local_cost_limits, 
    0.7 * req_cost_limit Global_cost_limits, top_pos_ok, poses_ok, [],
    fn X => emit( X, Trf_history ) )
end (* fun req_r *)
  


fun case_dist_r' MULTIR_or_R_trfs ( Current_program, 
  Trf_history as 
    CASE_DIST{ activated_poses, ... } :: _ : atomic_trf_record list,
  Local_cost_limits, Global_cost_limits, _, emit ) : unit =
let
  fun top_pos_ok R_top_poses =
    forall( fn R_top_pos => member( R_top_pos, activated_poses ), R_top_poses )

  fun is_ok( R_top_pos, R_bottom_poses ) =
    top_pos_ok[ R_top_pos ]

  fun poses_ok Xss = forall( is_ok, Xss )
in
  MULTIR_or_R_trfs( Current_program, Local_cost_limits, 
    0.7 * req_cost_limit Global_cost_limits, top_pos_ok, poses_ok, [],
    fn X => emit( X, Trf_history ) )
end (* fun case_dist_r *)
  


fun case_dist_abstr( Current_program, 
  Trf_history as 
    CASE_DIST{ activated_poses, ... } :: _ : atomic_trf_record list,
  Local_cost_limits, emit ) : unit =
let
  fun H_pos_ok H_pos = member( H_pos, activated_poses )
in
  ABSTR_trfs( Current_program, Local_cost_limits, H_pos_ok, fn _ => true, 
    fn X => emit( X, Trf_history ) )
end (* fun case_dist_abstr *)


fun start_r' MULTIR_or_R_trfs ( Current_program : dec, 
      nil : atomic_trf_record list, Local_cost_limits : real list, 
  Global_cost_limits : real list, _, emit ) =
  MULTIR_or_R_trfs( Current_program, Local_cost_limits, 
    0.7 * req_cost_limit Global_cost_limits,
    fn _ => true, fn _ => true, [], fn X => emit( X, nil ) )

fun mk_r_proc X_r' = other_proc(
  fn( Current_program : dec, Trf_history : atomic_trf_record list,
    Local_cost_limits : real list, emit ) =>
  X_r' R_trfs ( Current_program, Trf_history, Local_cost_limits, [1.0E99], 
                REQ_lib.dummy_req_match_error_data(),
                emit )
  )

val start_r_rule : rule_type =
  ( { Is_start=true, Is_end=true, Is_strong=true, Is_open=false,
      Atomic_trfs = [ R_trf ], Rule_id="start_r" },
    mk_r_proc start_r',
    100.0 )
    
val start_multir_rule : rule_type =
  ( { Is_start=true, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ MULTIR_trf ], Rule_id="start_multir" },
    REQ_proc( start_r' MULTIR_trfs ),
    10.0 )
    
val start_req_rule : rule_type =
  ( { Is_start=true, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ REQ_trf ], Rule_id="start_req" },
    REQ_proc start_req,
    10.0 )

val start_dupl_rule : rule_type =
  ( { Is_start=true, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ DUPL_trf ], Rule_id="start_dupl" },
    REQ_proc start_dupl,
    10.0 )
    
val start_case_dist_rule : rule_type =
  ( { Is_start=true, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ CASE_DIST_trf ], Rule_id="start_case_dist" },
    REQ_proc start_case_dist,
    10.0 )
    
val start_abstr_rule : rule_type =
  ( { Is_start=true, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ ABSTR_trf ], Rule_id="start_abstr" },
    other_proc start_abstr,
    10.0 )
    
    
val dupl_abstr_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ DUPL_trf, ABSTR_trf ], Rule_id="dupl_abstr" },
    other_proc dupl_abstr,
    10.0 )

val dupl_req_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ DUPL_trf, REQ_trf ], Rule_id="dupl_req" },
    REQ_proc dupl_req,
    10.0 )

    
val dupl_case_dist_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ DUPL_trf, CASE_DIST_trf ], Rule_id="dupl_case_dist" },
    REQ_proc dupl_case_dist,
    2.0 )

val dupl_r_rule : rule_type =
  ( { Is_start=false, Is_end=true, Is_strong=true, Is_open=false,
      Atomic_trfs = [ DUPL_trf, R_trf ], Rule_id="dupl_r" },
    mk_r_proc dupl_r',
    100.0 )
    
val dupl_multir_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ DUPL_trf, MULTIR_trf ], Rule_id="dupl_multir" },
    REQ_proc( dupl_r' MULTIR_trfs ),
    10.0 )


val abstr_req_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=false, Is_open=false,
      Atomic_trfs = [ ABSTR_trf, REQ_trf ], Rule_id="abstr_req" },
    REQ_proc abstr_req,
    10.0 )

val abstr_r_rule : rule_type =
  ( { Is_start=false, Is_end=true, Is_strong=false, Is_open=false,
      Atomic_trfs = [ ABSTR_trf, R_trf ], Rule_id="abstr_r" },
    mk_r_proc abstr_r',
    20.0 )

val abstr_multir_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=false, Is_open=true,
      Atomic_trfs = [ ABSTR_trf, MULTIR_trf ], Rule_id="abstr_multir" },
    REQ_proc( abstr_r' MULTIR_trfs ),
    5.0 )

val req_abstr_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ REQ_trf, ABSTR_trf ], Rule_id="req_abstr" },
    other_proc req_abstr,
    10.0 )


val req_abstr2_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ REQ_trf, ABSTR_trf ], Rule_id="req_abstr2" },
    other_proc req_abstr2,
    10.0 )

val case_dist_abstr_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ CASE_DIST_trf, ABSTR_trf ], Rule_id="case_dist_abstr" },
    other_proc case_dist_abstr,
    4.0 )


val case_dist_r_rule : rule_type =
  ( { Is_start=false, Is_end=true, Is_strong=true, Is_open=false,
      Atomic_trfs = [ CASE_DIST_trf, R_trf ], Rule_id="case_dist_r" },
    mk_r_proc case_dist_r',
    100.0 )

val case_dist_multir_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ CASE_DIST_trf, MULTIR_trf ], Rule_id="case_dist_multir" },
    REQ_proc( case_dist_r' MULTIR_trfs ),
    10.0 )

val req_r_rule : rule_type =
  ( { Is_start=false, Is_end=true, Is_strong=true, Is_open=false,
      Atomic_trfs = [ REQ_trf, R_trf ], Rule_id="req_r" },
    mk_r_proc req_r',
    100.0 )

val req_multir_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ REQ_trf, MULTIR_trf ], Rule_id="req_multir" },
    REQ_proc( req_r' MULTIR_trfs ),
    10.0 )

val multir_r_rule : rule_type =
  ( { Is_start=false, Is_end=true, Is_strong=true, Is_open=false,
      Atomic_trfs = [ MULTIR_trf, R_trf ], Rule_id="multir_r" },
    other_proc MULTIR_R.multir_r,
    40.0 )
    
    
val req_case_dist_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=true,
      Atomic_trfs = [ REQ_trf, CASE_DIST_trf ], Rule_id="req_case_dist" },
    REQ_proc req_case_dist,
    1.4 )

val abstr_case_dist_rule : rule_type =
  ( { Is_start=false, Is_end=false, Is_strong=true, Is_open=false,
      Atomic_trfs = [ ABSTR_trf, CASE_DIST_trf ], Rule_id="abstr_case_dist" },
    REQ_proc abstr_case_dist,
    2.0 )



local

val Coupling_rules = [
  start_r_rule, start_multir_rule, start_req_rule, start_dupl_rule,
    start_case_dist_rule, start_abstr_rule, 
  dupl_r_rule, dupl_multir_rule, dupl_req_rule, dupl_case_dist_rule, 
    dupl_abstr_rule, 
  abstr_r_rule, abstr_multir_rule, 
    abstr_req_rule, abstr_case_dist_rule,
  case_dist_r_rule, case_dist_multir_rule, case_dist_abstr_rule, 
  req_r_rule, req_multir_rule, req_case_dist_rule,
    req_abstr_rule, req_abstr2_rule,
  multir_r_rule
  ]
  

open Tree

fun form_to_string( ({Rule_id,...},_,_) : rule_type ) = Rule_id

fun is_start( ({Is_start,...},_,_) : rule_type ) = Is_start
fun is_end( ({Is_end,...},_,_) : rule_type ) = Is_end
fun is_strong( ({Is_strong,...},_,_) : rule_type ) = Is_strong
fun is_open( ({Is_open,...},_,_) : rule_type ) = Is_open
fun atomic_trfs( ({Atomic_trfs,...},_,_) : rule_type ) = Atomic_trfs
fun atomic_trf_match( T1, T2) = T1=T2 

fun open_check( So_far : rule_type tree ) : bool =
  forall( fn Pos =>
    let
      val Sub = pos_to_sub( So_far, Pos )
    in
      not( is_leaf Sub ) orelse not( is_open( root Sub ) )
    end,
    positions So_far )


exception Compound_trf_form_synt;
fun compound_trf_form_synt( Rules :  rule_type list )
  : rule_type tree list =
  let 
    fun synt( Is_end : bool,
          So_far :  rule_type tree, Rules :  rule_type list ) 
        : ( rule_type tree) list =
    let 
(*
      val _ = ( 
        nl(); 
        print_list( fn Form => p( form_to_string Form ), preorder So_far );
        p"\nIs_end = "; print_bool Is_end
        )
*)
    in
      if Is_end then
        if is_end( dh( preorder So_far ) ) andalso open_check So_far then 
          [ So_far ] 
        else 
          []
      else
        flat_map( fn Rule =>
          flat_map( fn Pos =>
            let val Rule' = root(pos_to_sub(So_far,Pos)) in
              if not( is_open(Rule') ) orelse
                 is_start(Rule) orelse
                 not( atomic_trf_match(
                        hd(atomic_trfs(Rule)),
                        dh(atomic_trfs(Rule'))
                        )) orelse
                 is_strong(Rule) andalso not( is_leaf(pos_to_sub(So_far,Pos)) )
              then
                nil
              else
                synt( is_end Rule,
                      add_sub_right(So_far,Pos,tree_cons(Rule,nil)),
                      filter( fn Rule' => not(rule_eq(Rule,Rule')), Rules ) )
              end,
            positions(So_far)
            ),
          Rules
          )
    end
  in
    flat_map( fn Rule => synt( is_end Rule, tree_cons(Rule,nil),Rules),
                filter(is_start,Rules) )
  end


in

val Forms = map( preorder, compound_trf_form_synt Coupling_rules )

end (* local *)


fun is_straight(  Form : rule_type list ) : bool =
  forall( fn( { Atomic_trfs, ... }, _, _ ) =>
    forall( fn A => A = R_trf orelse A = REQ_trf orelse A = CASE_DIST_trf,
      Atomic_trfs ),
    Form )

(*

val Forms = 
  if not( null Predefined.rec_types() ) then
    Forms
  else
    filter( is_straight, Forms )
  (* The use of TGI_args during expression synthesis means that a let-function 
     introduced by abstraction will never be allowed to be used if no
     recursive type exists.
  *)

*)

val Forms =  
  if not Test then Forms else
   [ start_dupl_rule, dupl_abstr_rule, abstr_req_rule, abstr_multir_rule, 
     multir_r_rule ] ::
(*
  [ start_multir_rule, multir_r_rule ] ::
   [start_req_rule,req_case_dist_rule,case_dist_abstr_rule,abstr_r_rule] ::
   [start_r_rule] ::
   [ start_dupl_rule, dupl_r_rule ] ::
   [start_abstr_rule,abstr_req_rule,abstr_r_rule] :: 
   [start_req_rule,req_abstr2_rule,abstr_r_rule] :: 
   [start_req_rule,req_abstr_rule,abstr_r_rule] :: 
   [start_r_rule] ::
   [ start_emb_rule, emb_r_rule ] ::
   [start_req_rule,req_abstr_rule,abstr_req_rule,abstr_r_rule] :: 
   [ start_abstr_rule, abstr_emb_rule, abstr_req_rule, abstr_r_rule ] ::
   [start_req_rule,req_case_dist_rule,case_dist_r_rule] ::
   [start_req_rule,req_abstr_rule,abstr_r_rule] :: 
   [start_case_dist_rule,case_dist_abstr_rule,abstr_req_rule,abstr_r_rule] ::
   [start_case_dist_rule,case_dist_abstr_rule,abstr_req_rule,abstr_r_rule] ::
   [ start_abstr_rule, abstr_r_rule ] ::
   [ start_case_dist_rule,case_dist_abstr_rule, abstr_r_rule ] ::
   [start_req_rule,req_r_rule] ::
   [ start_abstr_rule, abstr_emb_rule, abstr_r_rule ] ::
*)
  nil



val Forms = combine(fromto(0,length Forms-1),Forms)

local

(*

val N_straight = length( filter( fn( _, Form ) => is_straight Form, Forms ) )
val N_non_straight = length Forms - N_straight

fun consumption_weight( ( _, Form ) : form_type ) : real =
  if true (* N_non_straight = 0 *) then
    1.0 / real( length Forms )
  else if case Form of 
       [ ( { Rule_id, ... }, _, _ ) ] => Rule_id = "start_r"
     | _ => false
  then
    0.2
  else if is_straight Form then
    0.3 / real( N_straight - 1 )
  else
    0.5 / real N_non_straight
*)


exception Forms_length_exn
val N = length Forms
val () = if N mod 4 = 0 orelse Test then () else raise Forms_length_exn
(* 
N must be divisible by 4 since half of the forms start with dupl, 
half with start, half end with multir_r and half with only r
*)
val N = real N

fun consumption_weight( ( _, Form ) : form_type ) : real =
  if Test then 1.0/N else
let
  val ( { Rule_id, ... }, _, _ ) :: _ = Form
  val Dupl_factor = if Rule_id = "start_dupl" then 0.3 else 0.7
  val ( { Rule_id, ... }, _, _ ) = dh Form
  val Multir_factor = if Rule_id = "multir_r" then 0.3 else 0.7
in
  if case Form of 
       [ ( { Rule_id, ... }, _, _ ) ] => Rule_id = "start_r"
     | _ => false
  then
    0.3
  else
    Dupl_factor * Multir_factor / ( N / 4.0 )
end


val Consumption_weights = map( consumption_weight, Forms )

val Total_consumption_weight = real_sum Consumption_weights
val () = (
  p"\n\nTotal consumption weight = "; print_real Total_consumption_weight;
  nl(); nl() )
val Consumption_weights : real Array.array = Array.fromList Consumption_weights

in (* local *)

fun consumption_weight( Form_id : int ) : real =
  Array.sub( Consumption_weights, Form_id )
end

val _ = map( fn( Form_id, Form ) => ( 
  nl();
  output( !std_out, Real.toString( consumption_weight Form_id )  ^ " " );
  print_form( Form_id, Form )
  ),
  Forms )



fun emit_and_simplify( Current_program, Trf_history, emit ) : symbol list =
let
  val Current_program = unwrap Current_program
  val () = type_check_dec_raise Current_program
  val Value = Evaluate.program_eval_fun Current_program
  val () = No_of_compound_trf_synt_evals := !No_of_compound_trf_synt_evals + 1.0
  val _ = emit( Current_program, Trf_history, Value)
  val Value' = Value
  val ( Current_program, Value_opt ) = dead_code_elim Current_program
  val Value =
    case Value_opt of
      NONE => Value
    | SOME Value => Value
in
  emit( Current_program, Trf_history, Value );
  case beta_simplify_dec Current_program of
    NONE => ()
  | SOME( Current_program, Value_opt ) =>
      emit( Current_program, Trf_history,
        case Value_opt of NONE => Value | SOME Value => Value );
  make_set( filter( fn Sym => 
    is_not_activated_sym Sym andalso Sym <> PREDEFINED_NOT_ACTIVATED_SYMBOL, 
    #match_errors Value' ) )
end



type match_error_data = {
  overall_cost_limit : real,
  last_match_error_cost_limit_sum : real,
  current_sum : real ref }



fun handle_match_errors(
  First_call : bool,
  Data as { overall_cost_limit, last_match_error_cost_limit_sum,
            current_sum } : match_error_data,
  Cost_limit : real,
  Match_errors : symbol list,
  Current_program : dec,
  Trf_history : atomic_trf_record list,
  emit : dec * atomic_trf_record list * Evaluate.program_eval_type -> unit
  ) : unit =
  case Match_errors of
    [] => ()
  | Sym :: Syms =>
  let
    val Estimated_match_error_cost_limit_sum =
      Constants.Alpha * last_match_error_cost_limit_sum
    
    val () = 
      if First_call then current_sum := !current_sum + Cost_limit else ()

    val Match_error_cost_limit =
      if not First_call then Cost_limit else
      max2( op<, 3.0, max2( op<, Cost_limit,
        if last_match_error_cost_limit_sum < 300.0 orelse
           !current_sum > 0.6 * overall_cost_limit
        then
          0.0
        else
          Cost_limit / Estimated_match_error_cost_limit_sum * 
          0.2 * overall_cost_limit ) )
  in
    if Match_error_cost_limit < 2.0 then () else
  let
    val [ Top_pos ] = absolutely_all_poses_filter(
      fn app_exp{ func, ... } => func = Sym
       | _ => false,
      #exp Current_program)
    
    val K = REQ_lib.K_bis( Match_error_cost_limit, 1 )

    fun emit_dec( New_D, Cost, Not_act_syms, { synted_exp, bottom_labels } ) = 
      if is_q_exp synted_exp then () else
      let
        val Trf_history =
          R( { r_top_poses = ( [ Top_pos ], NONE ),
               bottom_poses = [],
               bottom_labels = [],
               synted_exp = synted_exp, 
               not_activated_syms = Not_act_syms
               },
             [] ) :: Trf_history

        val Match_errors = 
          emit_and_simplify( New_D, Trf_history, emit )

        val () = No_of_match_error_evals := !No_of_match_error_evals + 1.0
        
        val Cost = max2( op<, 2.0, K * ( Cost + real REQ_lib.Offset ) )

      in
        handle_match_errors( false, Data, Cost_limit / Cost, 
          make_set( Syms @ Match_errors ), New_D, Trf_history, emit )
      end
  in
    R.R_lib.replace( R.R_lib.Exp_synt.Synt_lib.synt_and_eval_time_per_exp(),
      Constants.Default_no_of_cases_distribution, false,
      [], [],  Current_program, Top_pos, [], 
      Match_error_cost_limit, nil, true, emit_dec )
  end
  end (* handle_match_errors *)


exception Interpret_forms

fun interpret_forms(
  REQ_match_error_data : REQ_lib.req_match_error_data,
  Data : match_error_data,
  Current_program : dec,
  Trf_history : atomic_trf_record list,
  Forms_and_cost_limits : ( form_type * real ) list,
  emit : dec * atomic_trf_record list * Evaluate.program_eval_type -> unit
  ) : unit =
  case wanted_check( Current_program, Trf_history, Forms_and_cost_limits ) of 
    () =>
  case filter( fn( ( Form_id, Form ), _ ) => null Form, 
               Forms_and_cost_limits ) of
    [ _ ] => 
      let 
        val Match_errors = 
          emit_and_simplify( Current_program, Trf_history, emit )
        val [ ( _, Cost_limit ) ] = Forms_and_cost_limits
      in
        if null Match_errors then () else (
          Match_error_count := !Match_error_count + 1.0;
          Match_error_cost_limit_sum := 
            !Match_error_cost_limit_sum + Cost_limit;
          handle_match_errors( true, Data, Cost_limit,
            Match_errors, Current_program, Trf_history, emit ) )
      end
  | [] =>
let
  val Forms_and_cost_limits =
    filter( fn( ( Form_id, Form ), Cost_limit ) =>
      real_prod( map( #3, Form ) ) < Cost_limit,
      Forms_and_cost_limits )

  val Next_rule_choices : rule_type list = make_set'( rule_eq,
    map( fn( ( _, Next_rule :: _ ), _ ) => Next_rule,
         Forms_and_cost_limits ) )
in
  loop( fn Next_rule as ( { Rule_id, ... }, Procedure, _ ) =>
    let
      val Forms_and_cost_limits = 
        flat_map( fn( ( Form_id, Rule :: Rules ), Cost_limit ) =>
          if rule_eq( Rule, Next_rule ) then
            [ ( ( Form_id, Rules ), Cost_limit ) ]
          else
            [],
        Forms_and_cost_limits )

      fun emit'( ( Next_program, Records, Cost_opts ), Trf_history ) =
        interpret_forms( REQ_match_error_data, Data, Next_program, 
          Records @ Trf_history,
          flat_map( fn( ( X, Cost_limit ), Cost_opt ) =>
            case Cost_opt of
              NONE => 
                ( case Records of [ R{ ... } ] => [ ( X, 0.0 ) ] | _ => [] )
            | SOME Cost =>
                if Cost < 0.001 then 
                  raise Interpret_forms 
                else
                  [ ( X, Cost_limit / max2( op<, 1.0, Cost ) ) ],
            combine( Forms_and_cost_limits, Cost_opts ) ),
          emit )

      val Local_cost_limits = map( fn( ( _, Form ), Cost_limit ) =>
        Cost_limit / real_prod( map( #3, Form ) ),
        Forms_and_cost_limits )
    in
    case Procedure of
      REQ_proc proc =>
        proc( Current_program, Trf_history, Local_cost_limits,
          map( fn( _, Cost_limit ) => Cost_limit, Forms_and_cost_limits ),
          REQ_match_error_data,
          emit' )
    | other_proc proc =>
        proc( Current_program, Trf_history, Local_cost_limits,
          emit' )
    end
    handle Ex => (
      p "\n\ninterpret_forms:\n";
      p  "  Current_program =\n"; Print.print_dec' Current_program; nl();
      p( "  Rule_id = " ^ Rule_id ^ "\n" );
      p "  Trf_history =\n "; print_trf_history Trf_history;
      nl();
      raise Ex ), 
    Next_rule_choices )
end (* fun interpret_forms *)

           

fun produce_children( Overall_cost_limit, Program, 
      Last_match_error_cost_limit_sum, REQ_match_error_data, emit ) =
case map( fn Pos => [Pos], 
       all_poses_filter( Rconst.is_rconst_exp, #exp Program ) ) of Alts =>
(*
if Overall_cost_limit < 10.0 * real( length Alts ) then
let
  fun emit'( D, Trf_history, _ ) = (
    emit( D, Trf_history, Evaluate.program_eval_fun D );
      No_of_compound_trf_synt_evals := !No_of_compound_trf_synt_evals + 1.0 )

in
  emit'( Synt_lib.NN_opt.opt( Program, Overall_cost_limit ), [], [] );
  Rconst.rconst_trfs( Program, Alts, [ Overall_cost_limit ], emit' );
  0.0
end
else
*)
let
  val Program = wrap Program
  val Current_sum = ref 0.0
  fun emit'( D, Trf_history, Eval ) = 
    emit( D, map( make_blastable, Trf_history ), Eval )
      handle Ex => (
      p "\n\nemit in produce_children:\n";
      p"\n  D =\n"; Print.print_dec' D; nl();
      p"\n  Trf_history = "; print_trf_history Trf_history;
      p"\n  Eval = "; Evaluate.print_quick_eval_value( 
        Evaluate.program_eval_type_to_quick Eval );
      p"\n";
      raise Ex )

     
in
  Overall_cost_limit_sum := !Overall_cost_limit_sum + Overall_cost_limit;
  interpret_forms( REQ_match_error_data,
    { overall_cost_limit = Overall_cost_limit,
      last_match_error_cost_limit_sum = Last_match_error_cost_limit_sum,
      current_sum = Current_sum
      },
    Program, 
    [],
    map( fn( Form_id, Form ) =>
      ( ( Form_id, Form ), Overall_cost_limit * consumption_weight Form_id ),
      Forms ),
    emit' );

  !Current_sum
end (* fun produce_children *)
    handle Ex => (
      p "\n\nproduce_children:\n";
      p"\n  Overall_cost_limit = "; print_real Overall_cost_limit;
      p"\n  Program =\n"; Print.print_dec' Program; nl();
      p"\n  Last_match_error_cost_limit_sum = "; 
        print_real Last_match_error_cost_limit_sum;
      p"\n  REQ_match_error_data = ";
        REQ_lib.print_req_match_error_data REQ_match_error_data;
      p"\n";
      raise Ex )


end (* functor Compound_trf_synt *)

