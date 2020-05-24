(* File: req.sml.
   Created 1998-09-08.
   Modified 1999-08-07.
*)

signature REQ_sig =
sig

val REQ_trfs :
  REQ_lib.req_match_error_data *
  Ast.dec *
  real list *
  real *
  ( Ast_lib.pos list -> bool ) *
  ( ( Ast_lib.pos * Ast_lib.pos list ) list -> bool ) *
  Ast.symbol list list *
  ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list -> unit )
  ->
  unit

structure R : R_sig

(* val is_bad : Ast.dec * Ast.dec * Ast_lib2.simple_R_record list -> bool *)

val print_req_match_error_statistics : unit -> unit
val map_time : unit -> real
end


functor REQ_fn( Exp_synt : EXP_SYNT ) : REQ_sig =
struct

open Lib List1 Ast Ast_lib Ast_lib2 Print 

structure REQ_lib2 = REQ_lib2_fn( Exp_synt )
(* val is_bad = REQ_lib2.is_bad *)
val map_time = REQ_lib2.map_time
val print_req_match_error_statistics = REQ_lib2.print_req_match_error_statistics
structure R = REQ_lib2.R
structure So_far = R.R_lib.So_far

fun make_emittable So_far =
  So_far.make_emittable( REQ_lib2.R.R_lib2.cse, So_far )

local

fun interval_widths(
      { REQ_record : REQ_record list, order_no : int },
      From_pq : bool,
      REQs_and_mults : ( REQ_record list * int ) list, (* PQ part only *)
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

  val Cost = real order_no  + real REQ_lib.Offset
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
let
  val Rs = flat_map( from_REQ_record, REQ_record )
in
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
    interval_widths( Y, true, REQs_and_mults, Simple_so_far, Cost_so_far, Xss )
in
  REQ_lib.choices_in_reqs_and_mults( 
    REQs_and_mults, 
    if From_pq then order_no else ~Max_int, 
    emit );
  true
end
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
  fn( PQ_reqs_and_mults : ( REQ_record list * int ) list,
      Other_reqs_and_mults : ( REQ_record list * int ) list,
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
    interval_widths( Y, true, PQ_reqs_and_mults, [], 1.0, Xss )
  fun emit2 Y =
    interval_widths( Y, false, PQ_reqs_and_mults, [], 1.0, Xss )
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
      Time_limit : real,
(* Needed when many REQs exists that cannot be combined. *)
      Cost_limits : real list,
      PQ_reqs_and_mults : ( REQ_record list * int ) list,
      Other_reqs_and_mults : ( REQ_record list * int ) list
      ) : real option list list (* K values *) =
let
  val Timer = mk_timer "normalize"
  val _ = start_timer Timer
 
(*
  val _ = p"\nCalling normalize\n"
*)
  val REQ_PQ_card = int_sum( map( #2, PQ_reqs_and_mults ) )
  val REQ_card = REQ_PQ_card + int_sum( map( #2, Other_reqs_and_mults ) )
  val Cost_limitss : real list list =
    map( fn Weight =>
      map( fn Cost_limit => Cost_limit * Weight, Cost_limits ),
      Constants.No_of_REQs_distribution )
  val K_optss : real option list list =
    map( fn( Cost_limits, N ) =>
      map( fn Cost_limit =>
        REQ_lib.estimate_K( REQ_card, REQ_PQ_card, Cost_limit, N ),
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
    val K_optss : real option list list = unpack K_opts
    val Xss =
      map( fn( ( Cost_limits, K_opts ), No_of_REQs ) =>
        map( fn( Cost_limit, NONE ) =>
                 { cost_limit = Cost_limit, k = 1.0, iw = ref( real Max_int ) }
             | ( Cost_limit, SOME K ) =>
                 { cost_limit = Cost_limit, k = K, iw = ref(

if K * ( real REQ_card + real REQ_lib.Offset ) * 
   real_pow( real REQ_PQ_card + real REQ_lib.Offset, real( No_of_REQs - 1 ) ) 
   < 0.1 
   orelse
   check_timer Timer > Time_limit andalso !F_called
then
  real Max_int
else
  0.0
  ) },

             combine( Cost_limits, K_opts ) ),
        combine( combine( Cost_limitss, K_optss ), 
                 fromto( 1, length Cost_limitss ) ) )

    val () = interval_widths( PQ_reqs_and_mults, Other_reqs_and_mults, Xss )

    val Y_optss =
      map( fn Xs =>
        map( fn{ iw, ... } =>
          if real_rep_eq( !iw, real Max_int ) then NONE else SOME( !iw - 1.0 ),
          Xs ),
        Xss )
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

(* Compute interval widths with scope checking and evaluation: *)

fun adjusted_interval_widths(
      { REQ_record : REQ_record list, order_no : int },
      From_pq : bool,
      REQs_and_mults : ( REQ_record list * int ) list, (* PQ part only *)
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
  val Cost = real order_no + real REQ_lib.Offset
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
  case So_far.new_so_far'( flat_map( from_REQ_record, REQ_record ), So_far ) of
    NONE => true
  | SOME So_far =>
let
  val ( D_so_far, _ ) = make_emittable So_far
  val Ok = not( null Xs ) andalso
    Exp_synt.Synt_lib.scope_check_dec D_so_far andalso
    is_REQ D_so_far
  val _ = 
    if Ok then
      loop( fn{ k, iw, ... } => iw := !iw + 1.0 / ( k * Cost_so_far ), Xs )
    else
      ()
  fun emit Y =
    adjusted_interval_widths( Y, true, REQs_and_mults, So_far, Cost_so_far, 
      Xss, is_REQ )
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
  p"REQ_record = \n"; print_list( print_REQ_record, REQ_record );
  p"\nD_so_far = "; Print.print_dec'( #2 So_far );
  re_raise( Ex, "" )
  )





in (* local *)

val adjusted_interval_widths =
  fn( PQ_reqs_and_mults : ( REQ_record list * int ) list,
      Other_reqs_and_mults : ( REQ_record list * int ) list,
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
    adjusted_interval_widths( Y, true, PQ_reqs_and_mults, So_far, 1.0, Xss, 
      is_REQ )
  fun emit2 Y =
    adjusted_interval_widths( Y, false, PQ_reqs_and_mults, So_far, 1.0, Xss, 
      is_REQ )
in
  REQ_lib.choices_in_reqs_and_mults( PQ_reqs_and_mults, ~Max_int, emit1 );
  REQ_lib.choices_in_reqs_and_mults( 
    PQ_reqs_and_mults @ Other_reqs_and_mults, 
    int_sum( map( #2, PQ_reqs_and_mults ) ),
    emit2 )
end
  
end (* local *)

    

fun produce_REQs(
      { REQ_record : REQ_record list, order_no : int },
      From_pq : bool,
      REQs_and_mults : ( REQ_record list * int ) list, (* PQ part only *)
      So_far : So_far.so_far,
      Cost_so_far : real,
      Xss : {
        adjustment_factor : real,
(* Computed using adjusted iw and Constants.No_of_REQs_distribution. *)
        cost_limit : real,
        k : real,
        iw :  real ref
        } option list list,
      is_REQ : dec -> bool,
      Records_so_far : REQ_record list,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : bool =
let
  val Cost = real order_no + real REQ_lib.Offset
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
  case So_far.new_so_far'( flat_map( from_REQ_record, REQ_record ), So_far ) of
    NONE => true
  | SOME So_far =>
let
  val ( D_so_far, Simple_R_and_cse_records ) = make_emittable So_far
  val Ok = not( forall( is_NONE, Xs ) ) andalso
    Exp_synt.Synt_lib.scope_check_dec D_so_far andalso
    is_REQ D_so_far
  val _ = 
    if Ok then
      loop( fn NONE => () 
             | SOME{ k, iw, adjustment_factor, ... } => 
                 iw := !iw + 1.0 / ( adjustment_factor * k * Cost_so_far ), 
            Xs )
    else
      ()
  val Records_so_far = REQ_record @ Records_so_far
  fun emit' Y =
    produce_REQs( Y, true, REQs_and_mults, So_far, Cost_so_far, 
      Xss, is_REQ, Records_so_far, emit )
in
  (
  if Ok then
    emit(
      D_so_far,
      [ REQ( Records_so_far, Simple_R_and_cse_records ) ],
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

structure E = Exp_synt.Synt_lib.Evaluate

fun eval_time_report Timer = (
  p( "\nTimer = " ^ Real.toString( check_timer Timer ) );
  p( "\nTime for is_bad = " ^ Real.toString( REQ_lib2.is_bad_time() ) );
  p( "\nIs REQ time = " ^ Real.toString( REQ_lib2.is_REQ_time() ) );
  p( "\nIs REQ eval time = " ^ Real.toString( REQ_lib2.is_REQ_eval_time() ) );
  p( "\nCum replace time = " ^ 
     Real.toString( REQ_lib2.R.R_lib.cum_replace_time() ) );
  p( "\nNo emitted by R = " ^ Int.toString( REQ_lib2.R.no_emitted_by_R() ) );
  p( "\nNo of evaluations = " ^ Real.toString( E.no_of_evaluations() ) );
  p( "\nCum eval time = " ^ Real.toString( E.cum_eval_time() ) );
  p( "\nCum pure exp synt time = " ^ 
     Real.toString( Exp_synt.cum_pure_exp_synt_time() ) );
  p( "\nCum exp synt time = " ^ Real.toString( Exp_synt.cum_exp_synt_time() ) );
  p( "\nAdd not activated exps time = " ^ 
     Real.toString( Exp_synt.Synt_lib.add_not_activated_exps_time() ) );
  nl() )


exception REQ_trfs_exn1
fun REQ_trfs(
      REQ_match_error_data,
      D : dec,
      Cost_limits : real list,
      REQ_cost_limit : real, 
      top_pos_ok : pos list -> bool,
      poses_ok : ( pos * pos list ) list -> bool,
      Min_once :  symbol list list,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : unit =
let
  val REQ_match_error_data_for_second_run = 
    REQ_lib.req_match_error_data_clone REQ_match_error_data
  val D = REQ_lib2.R.R_lib.add_not_activated_exps_dec D
  val Synt_and_eval_time_per_exp = 
    REQ_lib2.R.R_lib.Exp_synt.Synt_lib.synt_and_eval_time_per_exp()
  val Timer = mk_timer "REQ_trfs"
  val _ = start_timer Timer
  val ( Cum_map_data_opt, REQ_PQ_prefix, is_REQ ) =
    REQ_lib2.first_run( Synt_and_eval_time_per_exp,
      REQ_match_error_data, D, REQ_cost_limit, top_pos_ok, 
      poses_ok, Min_once, max( op<, Cost_limits ) )
(*
  val () = p"\n\nfirst_run finished!\n\n";
  val () = eval_time_report Timer
*)
  val PQ_reqs_and_mults : ( REQ_record list * int ) list = 
    map( fn REQ_PQ_node => ( #2 REQ_PQ_node, 1 ), REQ_PQ_prefix )

  val Other_reqs_and_mults : ( REQ_record list * int ) list = 
    case Cum_map_data_opt of
      NONE => []
    | SOME( _, Reqs_and_mults ) =>
        map( fn( REQ_PQ_node, Mult ) => ( #2 REQ_PQ_node, Mult ),
          Reqs_and_mults )

  val K_optss = 
    normalize( check_timer Timer + 
               max(op<, REQ_cost_limit::Cost_limits ) * 
               Exp_synt.Synt_lib.synt_and_eval_time_per_exp(),
      Cost_limits, PQ_reqs_and_mults, Other_reqs_and_mults )
(*
  val () = p"\n\nnormalize finished!\n\n";
  val () = eval_time_report Timer
*)
  val Cost_limitss : real list list =
    map( fn Weight =>
      map( fn Cost_limit => Cost_limit * Weight, Cost_limits ),
      Constants.No_of_REQs_distribution )

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

  val () = adjusted_interval_widths(
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
      combine( Constants.No_of_REQs_distribution, Xss ) )

  val Xss =
    map( fn( Weight, Xs ) =>
      map( fn( Untouched_iw, { cost_limit, k, iw } ) => 
        if real_rep_eq( !iw, real Max_int ) then
          NONE
        else if !iw > 1.06 then
          raise REQ_trfs_exn1
        else
          SOME{
            adjustment_factor = !iw / Weight /
              ( 1.0 + !Untouched_iw / ( 1.0 - !Untouched_iw ) ),
            cost_limit = cost_limit,
            k = k,
            iw = ref 0.0 },
        combine( Untouched_iws, Xs ) ),
      combine( Constants.No_of_REQs_distribution, Xss ) )

  val produce_REQs = fn( Y, From_pq ) =>
    produce_REQs( Y, From_pq, PQ_reqs_and_mults, 
      So_far.initial_so_far D, 1.0, Xss, is_REQ, [], emit )

  fun emit1 Y = produce_REQs( Y, true )

  val () = 
    REQ_lib.choices_in_reqs_and_mults( PQ_reqs_and_mults, ~Max_int, emit1 )
(*
  val () = p"\n\nemit1 finished!\n\n"
  val () = eval_time_report Timer
*)
  fun emit2{ order_no : int, req_node : REQ_lib2.req_node }  = 
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
      REQ_lib2.second_run( Synt_and_eval_time_per_exp,
        REQ_match_error_data_for_second_run, D, 
        REQ_cost_limit, top_pos_ok,
        poses_ok, Min_once, Cum_map_data, REQ_PQ_prefix, emit2 ) ) );
(* 
p"\nFinal IWs:\n";
loop( fn Xs => (
  nl();
  loop( fn NONE => p( " NONE" )
         | SOME{ iw, ... } => p( " " ^ Real.toString( !iw ) ), 
        Xs )
  ),
  Xss );
  eval_time_report Timer
*)
  delete_timer Timer
end (* fun REQ_trfs *)
handle Ex => (
  p"\n\nREQ_trfs:\n";
  p"  D = \n"; Print.print_dec' D; nl();
  p"  Cost_limits = "; print_real_list Cost_limits;
  p"  REQ_cost_limit = "; p( Real.toString REQ_cost_limit );
  nl();
  re_raise( Ex, "REQ_trfs" ) )
  
end (* functor REQ_fn *)
