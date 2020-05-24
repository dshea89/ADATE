(* File: multir.sml.
   Created 1999-07-20.
   Modified 1999-07-24.
   Analogous with req.sml.
*)

signature MULTIR_sig =
sig

val MULTIR_trfs :
  Ast.dec *
  real list *
  real *
  ( Ast_lib.pos list -> bool ) *
  ( ( Ast_lib.pos * Ast_lib.pos list ) list -> bool ) *
  Ast.symbol list list *
  ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list -> unit )
  ->
  unit

end

functor MULTIR_fn( R : R_sig ) : MULTIR_sig =
struct

open Lib List1 Ast Ast_lib Ast_lib2 Print 

structure MULTIR_lib2 = MULTIR_lib2_fn( R )
structure So_far = R.R_lib.So_far

fun location_cost( First_R : bool, Simples : simple_R_record list, 
      D_exp : exp ) : real =
  if First_R then 1.0 else
  let
    val Pos = longest_common_prefix( map( #top_pos, Simples ) )
  in
    real( exp_size( pos_to_sub( D_exp, Pos ) ) )
  end


fun cost( Order_no : int, First_R : bool, Simples : simple_R_record list,
      D_exp : exp ) : real =
  real( Order_no + REQ_lib.Offset ) * location_cost( First_R, Simples, D_exp ) 
  

local

fun interval_widths(
      D_exp : exp,
      { REQ_record : REQ_record, order_no : int },
      From_pq : bool,
      REQs_and_mults : ( REQ_record * int ) list, (* PQ part only *)
      Simple_so_far : simple_R_record list,
      Cost_so_far : real,
      Xss : {
        cost_limit : real,
        k : real,
        iw :  real ref
        } list list
      ) : bool =
let
(*
  val _ = p( "\ninterval_widths: " ) 
  val _ = loop( fn _ => p "x", fromto( 1, 5 - length Xss ) )
  val _ = p( " Cost_so_far = " ^ Real.toString Cost_so_far )
*)

  val Rs = from_REQ_record REQ_record
  val Cost = cost( order_no, null Simple_so_far, Rs@Simple_so_far, D_exp )
  val Xss =
    map( fn( Xs, I ) =>
      filter( fn{ cost_limit, k, iw } =>
        k * real_pow( Cost, real I ) * Cost_so_far < cost_limit andalso 
        !iw < 1.5,
        Xs ),
      combine( Xss, fromto(1, length Xss ) ) )
  val Cost_so_far = Cost * Cost_so_far
in
  if forall( null, Xss ) then
    false
  else
    case Xss of Xs::Xss =>
  if not( forall( fn Simple => 
       So_far.independent( Simple, Simple_so_far ),
       Rs ) )
  then
    true
  else
let
  val Simple_so_far = Rs @ Simple_so_far
  val _ = 
    loop( fn{ k, iw, ... } => iw := !iw + 1.0 / ( k * Cost_so_far ), Xs )
  fun emit Y =
    interval_widths( D_exp, Y, true, REQs_and_mults, 
      Simple_so_far, Cost_so_far, Xss )
in
  REQ_lib.choices_in_reqs_and_mults( 
    REQs_and_mults, 
    if From_pq then order_no else ~Max_int, 
    emit );
  true
end
end

in (* local *)

(* Xss format:

                           Cost limits

No of REQs  [
         1      [            ...                          ],
         2      [            ...                          ],
         3      [            ...                          ],
         4      [            ...                          ] ]
*)

val interval_widths =
  fn( D_exp : exp, PQ_reqs_and_mults : ( REQ_record * int ) list,
      Other_reqs_and_mults : ( REQ_record * int ) list,
      Xss : {
        cost_limit : real,
        k : real,
        iw :  real ref
        } list list
      ) =>
let
(*
  val _ = p"\nCalling interval_widths."
*)

  fun emit1 Y =
    interval_widths( D_exp, Y, true, PQ_reqs_and_mults, [], 1.0, Xss )
  fun emit2 Y =
    interval_widths( D_exp, Y, false, PQ_reqs_and_mults, [], 1.0, Xss )
in
  REQ_lib.choices_in_reqs_and_mults( PQ_reqs_and_mults, ~Max_int, emit1 );
  REQ_lib.choices_in_reqs_and_mults( 
    PQ_reqs_and_mults @ Other_reqs_and_mults, 
    int_sum( map( #2, PQ_reqs_and_mults ) ),
    emit2 )
end
  
end (* local *)



local

fun pack( Template : 'a option list list, Xss : 'b list list ) : 'b list =
  map( #2,
    filter(
      fn( NONE, _ ) => false
      | ( SOME _, _ ) => true,
      combine( flatten Template, flatten Xss ) )
    )

exception Unpack_exn
fun unpack( Template : 'a option list list, Xs : 'b option list ) 
    : 'b option list list =
if length( filter( is_SOME, flatten Template ) ) <> length Xs then
  raise Unpack_exn
else
let
  fun insert_NONE( Ts : 'a option list, Xs : 'b option list ) : 'b option list =
    case ( Ts, Xs ) of
      ( [], [] ) => []
    | ( T1 :: Ts1,  _ ) =>
    case T1 of
      NONE => NONE :: insert_NONE( Ts1, Xs )
    | SOME _ => case Xs of X1::Xs1 => X1 :: insert_NONE( Ts1, Xs1 )

  val Xs : 'b option list = insert_NONE( flatten Template, Xs )

  fun g( [], [] ) = []
    | g( Ts :: Tss, Xs ) = 
        take( length Ts, Xs ) :: g( Tss, drop( length Ts, Xs ) )
in
  g( Template, Xs )
end

in (* local *)

fun normalize(
      D_exp : exp,
      Time_limit : real,
(* Needed when many REQs exists that cannot be combined. *)
      Cost_limits : real list,
      PQ_reqs_and_mults : ( REQ_record * int ) list,
      Other_reqs_and_mults : ( REQ_record * int ) list
      ) : real option list list (* K values *) =
let
  val Timer = mk_timer "normalize"
  val _ = start_timer Timer
 
(*
  val _ = p"\nCalling normalize\n"
*)
  val D_exp_size = exp_size D_exp
  val REQ_PQ_card = int_sum( map( #2, PQ_reqs_and_mults ) )
  val REQ_card = REQ_PQ_card + int_sum( map( #2, Other_reqs_and_mults ) )
  val Cost_limitss : real list list =
    map( fn Weight =>
      map( fn Cost_limit => Cost_limit * Weight, Cost_limits ),
      Constants.MULTIR_distribution )
  val K_optss : real option list list =
    map( fn( Cost_limits, N ) =>
      map( fn Cost_limit =>
        case REQ_lib.estimate_K( REQ_card, REQ_PQ_card, Cost_limit, N ) of
          NONE => NONE
        | SOME Cost_limit => 
            SOME( Cost_limit / real_pow( real D_exp_size, real(N-1) ) ),
        Cost_limits ),
      combine( Cost_limitss, fromto( 1, length Cost_limitss ) )
      )
(*
  val _ = p"\nestimate_K calls finished\n"
*)
  val pack = fn Xss => pack( K_optss, Xss )
  val unpack = fn Xs => unpack( K_optss, Xs )
  val Starts = map( fn SOME K => K, pack K_optss )

  val F_called = ref false
  
  fun f( K_opts : real option list ) : real option list =
  let
(*
    val () = (
      p"\n\nK_opts = "; print_list( print_real_option, K_opts ); nl() 
      )
*)
    val K_optss : real option list list = unpack K_opts
    val Xss =
      map( fn( ( Cost_limits, K_opts ), No_of_REQs ) =>
        map( fn( Cost_limit, NONE ) =>
                 { cost_limit = Cost_limit, k = 1.0, iw = ref( real Max_int ) }
             | ( Cost_limit, SOME K ) =>
                 { cost_limit = Cost_limit, k = K, iw = ref(

if K * ( real REQ_card + real REQ_lib.Offset ) * 
   real_pow( real REQ_PQ_card + real REQ_lib.Offset, real( No_of_REQs - 1 ) ) 
   < 0.1 / real_pow( real D_exp_size, real( No_of_REQs - 1 ) )
   orelse
   check_timer Timer > Time_limit andalso !F_called
then (
(*
  p"\n K = "; print_real K;
  p"\nREQ_card = " ; print_int REQ_card;
  p"\nNo_of_REQs = " ; print_int No_of_REQs;
*)
  real Max_int
  )
else
  0.0
  ) },

             combine( Cost_limits, K_opts ) ),
        combine( combine( Cost_limitss, K_optss ), 
                 fromto( 1, length Cost_limitss ) ) )

    val () = 
      interval_widths( D_exp, PQ_reqs_and_mults, Other_reqs_and_mults, Xss )

    val Y_optss =
      map( fn Xs =>
        map( fn{ iw, ... } =>
          if real_rep_eq( !iw, real Max_int ) then NONE else SOME( !iw - 1.0 ),
          Xs ),
        Xss )
(*
   val _ = 
     loop( fn Xs =>
       loop( fn{ cost_limit, k, iw } => (
         p"\n           cost_limit = "; print_real cost_limit;
         p"\n           k = "; print_real k;
         p"\n           !iw = "; print_real( !iw ); 
         nl() ),
         Xs ),
       Xss )
    val () = p"\n----------------------------------\n"
*)      
  in
    F_called := true;
    pack Y_optss
  end (* fun f *)

  val Eps = 1.0E~7

  fun stop( K1 : real, K2 ) : bool = 
    K1 < Eps orelse K2 < Eps orelse Real.abs( K1 / K2 -1.0 ) < Eps orelse
    check_timer Timer > Time_limit

  val K_opts : real option list =
    Eq_solve_lib.eq_solve_is_start_list'( stop, false, f, 0.05, Starts )
in
  delete_timer Timer;
  unpack K_opts
end (* fun normalize *)

end (* local *)





local

(* Compute interval widths with scope checking: *)

fun adjusted_interval_widths(
      D_exp : exp,
      { REQ_record : REQ_record, order_no : int },
      From_pq : bool,
      REQs_and_mults : ( REQ_record * int ) list, (* PQ part only *)
      So_far : So_far.so_far,
      Cost_so_far : real,
      Xss : {
        cost_limit : real,
        k : real,
        iw :  real ref
        } list list,
      is_REQ : dec -> bool
      ) : bool =
let
  val Rs = from_REQ_record REQ_record
  val Simple_so_far = So_far.original_records So_far
  val Cost = cost( order_no, null Simple_so_far, Rs@Simple_so_far, D_exp )
  val Xss =
    map( fn( Xs, I ) =>
      filter( fn{ cost_limit, k, iw } =>
        k * real_pow( Cost, real I ) * Cost_so_far < cost_limit andalso 
        !iw < 1.5,
        Xs ),
      combine( Xss, fromto(1, length Xss ) ) )
  val Cost_so_far = Cost * Cost_so_far
in
  if forall( null, Xss ) then
    false
  else
    case Xss of Xs::Xss =>
  case So_far.new_so_far'( Rs, So_far ) of
    NONE => true
  | SOME So_far =>
let
  val ( D_so_far, _ ) = R.R_lib2.make_emittable So_far
  val Ok = not( null Xs ) andalso
    R.R_lib.Exp_synt.Synt_lib.scope_check_dec D_so_far
  val _ = 
    if Ok then
      loop( fn{ k, iw, ... } => iw := !iw + 1.0 / ( k * Cost_so_far ), Xs )
    else
      ()
  fun emit Y =
    adjusted_interval_widths( D_exp, Y, true, REQs_and_mults, So_far, 
      Cost_so_far, Xss, is_REQ )
in
  REQ_lib.choices_in_reqs_and_mults( 
    REQs_and_mults, 
    if From_pq then order_no else ~Max_int, 
    emit );
  true
end
end 
handle Ex => (
  p"\n\nadjusted_interval_widths:\n\n";
  p"REQ_record = \n"; print_REQ_record REQ_record;
  p"\nD_so_far = "; Print.print_dec'( #2 So_far );
  re_raise( Ex, "" )
  )





in (* local *)

val adjusted_interval_widths =
  fn( D_exp : exp, PQ_reqs_and_mults : ( REQ_record * int ) list,
      Other_reqs_and_mults : ( REQ_record * int ) list,
      Xss : {
        cost_limit : real,
        k : real,
        iw :  real ref
        } list list,
      is_REQ : dec -> bool,
      D : dec
      ) =>
let
  val So_far = So_far.initial_so_far D
  fun emit1 Y =
    adjusted_interval_widths(  D_exp, Y, true, PQ_reqs_and_mults, 
      So_far, 1.0, Xss, is_REQ )
  fun emit2 Y =
    adjusted_interval_widths( D_exp, Y, false, PQ_reqs_and_mults, 
      So_far, 1.0, Xss, is_REQ )
in
  REQ_lib.choices_in_reqs_and_mults( PQ_reqs_and_mults, ~Max_int, emit1 );
  REQ_lib.choices_in_reqs_and_mults( 
    PQ_reqs_and_mults @ Other_reqs_and_mults, 
    int_sum( map( #2, PQ_reqs_and_mults ) ),
    emit2 )
end
  
end (* local *)

    

fun produce_REQs( D_exp : exp,
      { REQ_record : REQ_record, order_no : int },
      From_pq : bool,
      REQs_and_mults : ( REQ_record * int ) list, (* PQ part only *)
      So_far : So_far.so_far, Original_R_records : R_record list,
      Cost_so_far : real,
      Xss : {
        adjustment_factor : real,
(* Computed using adjusted iw and Constants.MULTIR_distribution. *)
        cost_limit : real,
        k : real,
        iw :  real ref
        } option list list,
      is_REQ : dec -> bool,
      Records_so_far : REQ_record list,
      emit : So_far.so_far * R_record list * real option list -> unit
      ) : bool =
let
  val Original_R_records = REQ_record :: Original_R_records
  val Rs = from_REQ_record REQ_record
  val Simple_so_far = So_far.original_records So_far
  val Cost = cost( order_no, null Simple_so_far, Rs@Simple_so_far, D_exp )
  val Xss =
    map( fn( Xs, I ) =>
      map( fn NONE => NONE
            | SOME( X as { cost_limit, k, iw, ... } ) =>
        if k * real_pow( Cost, real I ) * Cost_so_far < cost_limit andalso 
           !iw < 1.5
        then
          SOME X
        else
          NONE,
        Xs ),
      combine( Xss, fromto(1, length Xss ) ) )
  val Cost_so_far = Cost * Cost_so_far
in
  if forall( fn Xs => forall( is_NONE, Xs ), Xss ) then
    false
  else
    case Xss of Xs::Xss =>
  case So_far.new_so_far'( Rs, So_far ) of
    NONE => true
  | SOME So_far =>
let
  val ( D_so_far, Simple_R_and_cse_records ) = R.R_lib2.make_emittable So_far
  val Ok = not( forall( is_NONE, Xs ) ) andalso
    R.R_lib.Exp_synt.Synt_lib.scope_check_dec D_so_far 
  val _ = 
    if Ok then
      loop( fn NONE => () 
             | SOME{ k, iw, adjustment_factor, ... } => 
                 iw := !iw + 1.0 / ( adjustment_factor * k * Cost_so_far ), 
            Xs )
    else
      ()
  val Records_so_far = REQ_record :: Records_so_far
  fun emit' Y =
    produce_REQs( D_exp, Y, true, REQs_and_mults, So_far, Original_R_records,
      Cost_so_far, Xss, is_REQ, Records_so_far, emit )
in
  (
  if Ok then
    emit( So_far, Original_R_records,
      map( fn NONE => NONE
            | SOME{ adjustment_factor, k, ... } =>
                SOME( adjustment_factor * k * Cost_so_far ),
           Xs )
      )
  else
    () );
  REQ_lib.choices_in_reqs_and_mults( 
    REQs_and_mults, 
    if From_pq then order_no else ~Max_int, 
    emit' );
  true
end
end (* fun produce_REQs *)
handle Ex => (
  p"\n\nproduce_REQs:\n";
  p( "\norder_no = " ^  Int.toString( order_no ) );
  p( "\nCost_so_far = " ^ Real.toString( Cost_so_far ) );
  loop( fn Xs => (
    nl();
    loop( fn NONE => p( " NONE" )
           | SOME{ adjustment_factor, cost_limit, k, iw } => (
           p( "\n\nadjustment_factor = " ^ Real.toString( adjustment_factor ) );
           p( "\ncost_limit = " ^ Real.toString( cost_limit ) );
           p( "\nk = " ^ Real.toString( k ) );
           p( "\n!iw = " ^ Real.toString( !iw ) ^ "\n" ) ),
        Xs )
    ),
  Xss );
  re_raise( Ex, "produce_REQs" )
  )

structure E = R.R_lib.Exp_synt.Synt_lib.Evaluate

fun eval_time_report Timer = (
  p( "\nTimer = " ^ Real.toString( check_timer Timer ) );
  p( "\nMap time = " ^ Real.toString( MULTIR_lib2.map_time() ) );
  p( "\nSplay time = " ^ Real.toString( Splay_lib.splay_time() ) );
  p( "\nCum replace time = " ^ 
     Real.toString( R.R_lib.cum_replace_time() ) );
  p( "\nNo emitted by R = " ^ Int.toString( R.no_emitted_by_R() ) );
  p( "\nNo of evaluations = " ^ Real.toString( E.no_of_evaluations() ) );
  p( "\nCum eval time = " ^ Real.toString( E.cum_eval_time() ) );
  p( "\nCum pure exp synt time = " ^ 
     Real.toString( R.R_lib.Exp_synt.cum_pure_exp_synt_time() ) );
  p( "\nCum exp synt time = " ^ Real.toString( R.R_lib.Exp_synt.cum_exp_synt_time() ) );
  p( "\nAdd not activated exps time = " ^ 
     Real.toString( R.R_lib.Exp_synt.Synt_lib.add_not_activated_exps_time() ) );
  nl() )

fun new_min_once( Min_once : symbol list list, Simples : simple_R_record list )
    : symbol list list =
  filter( fn Syms =>
    not( exists( fn Sym =>
      exists( fn{ synted_exp, ... } => sym_exp_member( Sym, synted_exp ),
              Simples ),
      Syms ) ),
    Min_once )

exception MULTIR_trfs_exn1
fun MULTIR_trfs(
      D : dec,
      Cost_limits : real list,
      REQ_cost_limit : real, 
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool, Min_once : symbol list list,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : unit =
let
  val Synt_and_eval_time_per_exp = R.R_lib.Exp_synt.Synt_lib.synt_and_eval_time_per_exp()
  val D = R.R_lib.add_not_activated_exps_dec D
  val Timer = mk_timer "MULTIR_trfs"
  val _ = start_timer Timer
  val ( Cum_map_data_opt, REQ_PQ_prefix, is_REQ ) =
    MULTIR_lib2.first_run( Synt_and_eval_time_per_exp,
      D, REQ_cost_limit, top_pos_ok, poses_ok,
      max( op<, Cost_limits ) )
(*
  val () = p"\n\nfirst_run finished!\n\n";
  val () = eval_time_report Timer
*)
  val PQ_reqs_and_mults : ( REQ_record * int ) list = 
    map( fn REQ_PQ_node => ( #2 REQ_PQ_node, 1 ), REQ_PQ_prefix )

  val Other_reqs_and_mults : ( REQ_record * int ) list = 
    case Cum_map_data_opt of
      NONE => []
    | SOME( _, Reqs_and_mults ) =>
        map( fn( REQ_PQ_node, Mult ) => ( #2 REQ_PQ_node, Mult ),
          Reqs_and_mults )

  val K_optss = 
    normalize( #exp D, check_timer Timer + 
               max(op<, REQ_cost_limit::Cost_limits ) * 
               R.R_lib.Exp_synt.Synt_lib.synt_and_eval_time_per_exp(),
      Cost_limits, PQ_reqs_and_mults, Other_reqs_and_mults )
(*
  val () = p"\n\nnormalize finished!\n\n";
  val () = eval_time_report Timer
*)
  val Cost_limitss : real list list =
    map( fn Weight =>
      map( fn Cost_limit => Cost_limit * Weight, Cost_limits ),
      Constants.MULTIR_distribution )

  val Xss =
    map( fn( Cost_limits, K_opts ) =>
      map( fn( Cost_limit, K_opt ) =>
        case K_opt of
          NONE =>
            { cost_limit = Cost_limit, k = 1.0, iw = ref( real Max_int ) } 
        | SOME K =>
            { cost_limit = Cost_limit, k = K, iw = ref 0.0 },
        combine( Cost_limits, K_opts ) ),
      combine( Cost_limitss, K_optss ) )

  val () = adjusted_interval_widths( #exp D,
    PQ_reqs_and_mults,
    Other_reqs_and_mults,
    Xss,
    is_REQ,
    D )

(*
val () = p"\nIWs after adjusted_interval_widths:\n";
val () =
  loop( fn Xs => (
    nl();
    loop( fn{ iw, ... } => p( " " ^ Real.toString( !iw ) ), Xs )
    ),
    Xss )

  val () = eval_time_report Timer
*)
  val Untouched_iws = map( fn _ => ref 0.0, Cost_limits )
  val _ =
    map( fn( Weight, Xs ) =>
      map( fn( Untouched_iw, { iw, ... } ) => 
        if real_rep_eq( !iw, real Max_int ) then
          Untouched_iw := !Untouched_iw + Weight
        else
          (),
        combine( Untouched_iws, Xs ) ),
      combine( Constants.MULTIR_distribution, Xss ) )

  val Xss =
    map( fn( Weight, Xs ) =>
      map( fn( Untouched_iw, { cost_limit, k, iw } ) => 
        if real_rep_eq( !iw, real Max_int ) then
          NONE
        else if !iw > 1.06 then
          raise MULTIR_trfs_exn1
        else
          SOME{
            adjustment_factor = !iw / Weight /
              ( 1.0 + !Untouched_iw / ( 1.0 - !Untouched_iw ) ),
            cost_limit = cost_limit,
            k = k,
            iw = ref 0.0 },
        combine( Untouched_iws, Xs ) ),
      combine( Constants.MULTIR_distribution, Xss ) )

  fun emit'( So_far, Original_R_records, Cost_opts ) =
    emit( 
      D, (* Original dec fed to MULTIR_trfs. New D is in So_far. *)
      [ MULTIR{
          so_far = So_far,
          original_r_records = Original_R_records,
          new_min_once = 
            new_min_once( Min_once, So_far.original_records So_far ),
          top_pos_ok' = top_pos_ok,
          poses_ok' = poses_ok
          } ],
      Cost_opts )
    

  val produce_REQs = fn( Y, From_pq ) =>
    produce_REQs( #exp D, Y, From_pq, PQ_reqs_and_mults, 
      So_far.initial_so_far D, [], 1.0, Xss, is_REQ, [], emit' )

  fun emit1 Y = produce_REQs( Y, true )

  val () = 
    REQ_lib.choices_in_reqs_and_mults( PQ_reqs_and_mults, ~Max_int, emit1 )
(*
  val () = p"\n\nemit1 finished!\n\n"
  val () = eval_time_report Timer
*)
  fun emit2{ order_no : int, req_node : MULTIR_lib2.req_node }  = 
    ( produce_REQs( { order_no = order_no, REQ_record = #2 req_node }, false );
      () )
    handle Ex => (
      p"\nemit2:\n";
      re_raise( Ex, "emit2" ) )
in (
  case Cum_map_data_opt of
    NONE => ()
  | SOME( Cum_map_data, _ ) => (
      (* p"\n\nsecond run started...\n\n"; *)
      MULTIR_lib2.second_run( Synt_and_eval_time_per_exp,
        D, REQ_cost_limit, top_pos_ok, poses_ok,
        Cum_map_data, REQ_PQ_prefix, emit2 ) ) );
 (* 
p"\nFinal IWs:\n";
loop( fn Xs => (
  nl();
  loop( fn NONE => p( " NONE" )
         | SOME{ iw, ... } => p( " " ^ Real.toString( !iw ) ), 
        Xs )
  ),
  Xss );
  eval_time_report Timer;
*)
  delete_timer Timer
end (* fun MULTIR_trfs *)
handle Ex => (
  p"\n\nMULTIR_trfs:\n";
  p"  D = \n"; Print.print_dec' D; nl();
  p"  Cost_limits = "; print_real_list Cost_limits;
  p"  REQ_cost_limit = "; p( Real.toString REQ_cost_limit );
  nl();
  re_raise( Ex, "MULTIR_trfs" ) )
  
end (* functor MULTIR_fn *)
