(* File: trace_chain.sml
   Created: 1998-01-09
   Modified: 2000-03-14

  Find the total no of evaluations required to trace a genealogical chain.
*)


functor Trace_chain_functor( Spec : SPEC ) :
  sig
    val raw_trace : string * (string * string) list * string -> unit
  end =
struct

structure Compound_trf_synt = Compound_trf_synt_functor( Spec )
open Lib List1 Ast Ast_lib Ast_lib2 Compound_trf_synt.Exp_synt.Synt_lib.Evaluate


fun find_child( Trace_anc : TextIO.outstream,
      p : string -> unit, Parent : dec, Child : dec ) 
  : real =
(*
  Returns the no of evaluations executed during compound_trf_synt until a 
  child that is not worse than Child according to any pe is found.
*)
let
  val Saved_no_of_evaluations = no_of_evaluations()
  val N_evaluations = ref 0.0
  val Found = ref false
  val Old_child_eval = mk_eval_value_max Child
  (* Dummy values: *)
  val Best_child = ref Dummy_dec
  val Best_trf_history : atomic_trf_record list ref = ref []
  val Best_eval = ref Old_child_eval

  fun emit( New_D, Trf_history, Eval ) =
  let
    val New_child_eval = program_eval_to_eval_value( New_D, Eval ) 
  in
    if better_or_equal( New_child_eval, Old_child_eval ) then
      if !Found then  
        if main_syntactic_complexity New_child_eval <
           main_syntactic_complexity( !Best_eval )
        then (
          Best_child := New_D;
          Best_trf_history := Trf_history;
          Best_eval := New_child_eval
          )
        else
          ()
      else (
        N_evaluations := no_of_evaluations() - Saved_no_of_evaluations;
        Found := true;
        Best_child := New_D;
        Best_trf_history := Trf_history;
        Best_eval := New_child_eval
        )
    else
      ()
  end (* fun emit *)

  val Last_cost_limit = ref 0.0

  fun search( Cost_limit : real, Last_sum : real, REQ_match_error_data,
         Cutoffs_list ) 
      : unit =
    if !Found then () else
    let
      val () = p( Real.toString Cost_limit ^ " " )
      val  () = set_initial_idpef_arg Cutoffs_list
      val Sum =
        Compound_trf_synt.produce_children( 
          Cost_limit, Parent, Last_sum, REQ_match_error_data, emit )
    in
      Last_cost_limit := Cost_limit;
      search( Constants.Alpha * Cost_limit, Sum, 
        REQ_lib.next_req_match_error_data REQ_match_error_data,
        next_cutoffs_list() )
    end
  val Saved_stream = !std_out
in
  search( 1.0E4, 0.0, REQ_lib.initial_req_match_error_data(),
    First_cutoffs_list );
  std_out := Trace_anc;
  output( !std_out,
    "\n\n----------------------------------------------------------------\n\n" 
    );
  print_eval_value( !Best_eval ); nl();nl();
  Print.print_dec'( !Best_child ); nl();nl();
  print_trf_history( !Best_trf_history ); 
  output( !std_out, "\n\nCost limit = " ); print_real( !Last_cost_limit );
  std_out := Saved_stream;
  !N_evaluations
end (* fun find_child *)
      
fun trace( Trace_anc : TextIO.outstream,
      p : string -> unit, Chain : (string * dec) list ) : real =
  case Chain of
    [] => 0.0
  | [ _ ] => ( p "\n"; 0.0 )
  | ( Pid, P ) :: ( Cid, C ) :: Chain => (
      p( Pid ^ " to " ^ Cid ^ " : " ); 
      case find_child( Trace_anc, p, P, C ) of N_evaluations => (
        p( "  N_evaluations = " ^ Real.toString N_evaluations ^ "\n" );
        N_evaluations + trace( Trace_anc, p, ( Cid, C ) :: Chain )
        ) )

fun raw_trace( Spec_name : string, Chain as _::_  : (string * string) list,
      Main_log_file : string ) : unit =
(* Prints local log info to Spec_name.trace_log.
   Prints trace value with two significant digits to Main_log_file
*)
let
  fun rename_dec D = set_exp( D, rename( #exp D, false ) )
  val Chain as ( _, D1 ) :: _ = 
    map( fn( Id, D ) => 
      ( Id, rename_dec( Predefined.mk_f_dec D ) ), Chain )
  val () = loop( fn _ => program_eval_fun_max D1, fromto(1,100) )
  val Trace_log = TextIO.openAppend( Spec_name ^ ".trace_log" )
  fun p( S : string ) : unit = (
    TextIO.output( Trace_log, S );
    TextIO.flushOut Trace_log 
    )
  
  val () = p"\n\n"
  val Trace_anc = TextIO.openOut( Spec_name ^ ".trace_anc" )
  val N_evaluations = trace( Trace_anc, p, Chain )
  val Main_log = TextIO.openAppend Main_log_file
in
  TextIO.closeOut Trace_log;
  TextIO.output( Main_log, Real.fmt (StringCvt.SCI( SOME 1 )) N_evaluations ^ 
    " " );
  TextIO.closeOut Main_log
end

      

end (* functor Trace_chain *)
