(* File: genealogical_search.sml.
   Created 1993-07-19.
   Modified 2002-11-14.
*)

functor GFn( Spec : SPEC ) : 
  sig 
    val start : unit -> unit 
    val restart : unit -> unit
    val export : unit -> unit
    val export_restart : unit -> unit
    val mpi_start : unit -> unit 
    val mpi_restart : unit -> unit 
(*
    val restart_old : string * string * string * string -> unit
*)
  end =
struct

(* val Is_smlnj = C_interface.Is_smlnj *)

fun pid() = Int.toString( SysWord.toIntX( Posix.Process.pidToWord(
  Posix.ProcEnv.getpid() ) ) )

val Spec_name = 
let
  val S = Spec.Spec_file_name
  val L = String.size S
in
  if L-5 > 0 then String.extract( S, 0, SOME(L-5) ) else S
end

open Lib List1 Ast Ast_lib Ast_lib2 Print Parse
structure Compound_trf_synt = Compound_trf_synt_functor( Spec )
structure Synt_lib = Compound_trf_synt.Exp_synt.Synt_lib
structure Exp_synt = Compound_trf_synt.Exp_synt
structure Indis = Indis_functor( structure Synt_lib = Synt_lib )
structure Population_struct = 
  Population_functor( structure Indis = Indis (* structure NN_opt = Synt_lib.NN_opt *) )
open Synt_lib Indis.Evaluate.Spec Indis.Evaluate SplayTree 
  Genealogical_search_lib Indis Population_struct

val Genealogical_search_timer = mk_timer("Genealogical_search_timer")
val Normal_insert_timer = mk_timer("Normal_insert_timer")
val Handle_knocked_out_timer = mk_timer("Handle_knocked_out_timer")
val Would_be_inserted_timer = mk_timer("Would_be_inserted_timer")
val Bests_insert_check_timer = mk_timer("Bests_insert_check_timer")
val Simplify_loop_timer = mk_timer("Simplify_loop_timer")
val Choose_parents_timer = mk_timer("Choose_parents_timer")
val Expand_parent_timer = mk_timer("Expand_parent_timer")
val Expand_parent_timer' = mk_timer("Expand_parent_timer'")
val Petev_timer = mk_timer("Petev_timer")
val Mk_indi_timer = mk_timer("Mk_indi_timer")


fun print_eval_time_report() =
  let fun p S = output(!std_err,S)
  in
    p("\n\nGlobal time = "^Real.toString(check_timer Global_timer)^"\n");
    p("No of evaluations = "^Real.toString(Evaluate.no_of_evaluations())^"\n");
    p("Cumulative eval time = "^Real.toString(Evaluate.cum_eval_time())^"\n");
    p("Cumulative execution time including sml overhead= "^
       Real.toString(Evaluate.total_execute_time())^"\n");
    p("Cumulative finish time in execute.sml = "^
       Real.toString(Evaluate.finish_time())^"\n");
    p("Cumulative compile, assemble link and load time = "^
          Real.toString(Evaluate.compile_etc_time())^"\n");
    p("Cumulative pure exp synt time = " ^ 
      Real.toString(Exp_synt.cum_pure_exp_synt_time())^"\n");
    p("Cumulative exp synt time = " ^ 
      Real.toString(Exp_synt.cum_exp_synt_time())^"\n");
    p("Cumulative small exp synt time = " ^ 
      Real.toString(Exp_synt.cum_small_exp_synt_time())^"\n\n");
    p("Genealogical search time = " ^ 
      Real.toString(check_timer Genealogical_search_timer)^"\n");
    p("Normal insert time = " ^ 
      Real.toString(check_timer Normal_insert_timer)^"\n");
    p("Handle knocked out time = " ^ 
      Real.toString(check_timer Handle_knocked_out_timer)^"\n");
    p("Would be inserted time = " ^ 
      Real.toString(check_timer Would_be_inserted_timer)^"\n");
    p("Bests insert check time = " ^ 
      Real.toString(check_timer Bests_insert_check_timer)^"\n");
    p("Choose parents time = " ^ 
      Real.toString(check_timer Choose_parents_timer)^"\n");
    p("Expand parent time = " ^ 
      Real.toString(check_timer Expand_parent_timer)^"\n");
    p("Petev time = " ^ 
      Real.toString(check_timer Petev_timer)^"\n");
    p("Mk_indi time = " ^ 
      Real.toString(check_timer Mk_indi_timer)^"\n");
    p("Expand parent time' = " ^ 
      Real.toString(check_timer Expand_parent_timer')^"\n");
    p("Simplify loop time = " ^ 
      Real.toString(check_timer Simplify_loop_timer)^"\n\n");
    flush_out( !std_out )
  end


val Trace_stream = std_err
val Check_point_directory = ref "FooBar"

val Trace_file_name = ref "trace_file"
val Log_file_name = ref "log_file"    

fun open_files() =
  case !Trace_file_name of Trace_file =>
  case !Log_file_name of Log_file => (
      std_err := TextIO.openAppend Trace_file 
        handle Ex => (
          output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Trace_file ^
            "\n\n" );
          raise Ex
          );
      std_out := TextIO.openAppend Log_file 
        handle Ex => (
          output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Log_file ^
            "\n\n" );
          raise Ex
          ) )

val Total_cost_limit_sum = ref 0.0

local 

val Rand = Random.rand( ~836212, ~726256 )
val next = fn() => Random.randReal Rand * 0.5 + 0.75

val Save_info = map( fn I => 
  ( 1.0E7  * 
    real_pow( 2.0, real I ) * Random.randReal Rand, 
    ref 0.0, 
    Spec_name ^ "." ^ Int.toString I ^ "." ^ pid() ),
  fromto( 0, 512 ) )

val Last_check_cost_limit_sum = ref 0.0
val Last_global_time = ref 0.0
fun recalibrate() =
    if check_timer Global_timer - !Last_global_time < 1.0e4 then () else (
      initialize_approximate_synt_time_per_exp();
      Last_global_time := check_timer Global_timer
      )
  
in

fun checkpoint( Population : population ) = 
  case check_timer Global_timer of Global_time =>
  if !Total_cost_limit_sum - !Last_check_cost_limit_sum < 1.0E4 then () else
  case check_timer Genealogical_search_timer of Genealogical_search_time =>
  let
    val () = recalibrate()
    fun save( Interval, Save_cost_limit_sum, File_name ) =
      if !Total_cost_limit_sum - !Save_cost_limit_sum > Interval then
        if true then (
          Population_struct.save( Population, 
            !Check_point_directory ^ "/" ^ File_name,
            Genealogical_search_time, Global_time, 
            Equalizer.getConsumption() );
          Save_cost_limit_sum := !Total_cost_limit_sum
          )
        else (
          TextIO.closeOut( !std_out );
          TextIO.closeOut( !std_err );
          prepare_timers_for_export();
          if C_interface.exportML( File_name ^ ".mlton"  ) then (
            recover_timers_from_export();
            open_files();
            Evaluate.reinitialize Spec.Spec_file_name;
            Save_cost_limit_sum := !Total_cost_limit_sum;
            output(!std_out,"\n\nSTARTING EXECUTION\n")
            )
          else (
            recover_timers_from_export();
            open_files();
            Save_cost_limit_sum := !Total_cost_limit_sum
            )
        )
      else
        ()
  in
    Last_check_cost_limit_sum := !Total_cost_limit_sum;
    loop( save, Save_info )
  end

fun refresh_save_info() = 
  loop( fn( _, Save_cost_limit_sum, _ ) => 
    Save_cost_limit_sum := !Total_cost_limit_sum, 
    Save_info )

end (* local *)
    
structure S = Individual_set


val Normal_insert_count = ref 0
val Would_be_inserted_count = ref 0

exception Normal_insert_exn

val bests_insert_check = fn X =>
let
  val () = start_timer Bests_insert_check_timer
  val Y = bests_insert_check X
in
  stop_timer Bests_insert_check_timer;
  Y
end

fun normal_insert( X : individual, Population : population, 
      Knocked_out : S.set ) : population =
  let
    val _ = inc Normal_insert_count
    val () = start_timer Would_be_inserted_timer
    val Would_be_inserted =
      bests_insert_check( X, Population ) orelse
      all_class_insert_check( X, Population )

    val () = stop_timer Would_be_inserted_timer
  in
  if not Would_be_inserted then
    Population
  else
  let
    val _ = inc Would_be_inserted_count
    val _ = stop_timer Genealogical_search_timer
    val X = reevaluate X
    val _ = start_timer Genealogical_search_timer
    val () = best_update X
    val ( Knocked_out_indiss, New_pop ) = 
      bests_insert( X, Population )
    val Population = all_class_insert( X, New_pop )
  in
    loop( fn Knocked_out_indis =>
      case Knocked_out_indis of
        nil => ()
      | [ Y ] =>
          if #individual_id X = #individual_id Y then
            ()
          else
            S.insert( Y, Knocked_out )
      | Ys =>
          if exists( fn Y => #individual_id X = #individual_id Y, Ys ) then
            raise Normal_insert_exn
          else
            loop( fn Y => S.insert( Y, Knocked_out ), Ys ),
      Knocked_out_indiss );
    Population
  end
  end

val normal_insert = fn X =>
let
  val () = start_timer Normal_insert_timer
  val Y = normal_insert X
  val () = stop_timer Normal_insert_timer
in
  Y
end

fun handle_knocked_out( Population : population, Knocked_out : S.set ) 
    : population =
(* To be run when expansion of the current parent is finished and 
   end_lcss has been run.
*)
  let
    val Pop = ref Population
  in
    loop( fn X => 
        Pop:= knocked_out_all_class_insert( X, !Pop), 
      S.set_to_list Knocked_out  );
    !Pop
  end
    
val handle_knocked_out = fn X =>
let
  val () = start_timer Handle_knocked_out_timer
  val Y = handle_knocked_out X
  val () = stop_timer Handle_knocked_out_timer
in
  Y
end
  
val simplify_loop = fn X =>
let
  val () = start_timer Simplify_loop_timer
  val Y = simplify_loop X
  val () = stop_timer Simplify_loop_timer
in
  Y
end
  

local

val Best_validated : eval_value_type option ref = ref NONE

in

fun update_validation( Population : population ) : unit =
  loop( fn Indi =>
    if is_NONE( !( #validation_eval_value Indi ) ) then
    let
      val D = #program Indi
      val Validation_ev = 
        program_eval_to_eval_value( D, program_eval_fun_validate D )
    in
      #validation_eval_value Indi := SOME Validation_ev;
      case !Best_validated of
        NONE => Best_validated := SOME Validation_ev
      | SOME Best =>
      case pe5_cmp( Validation_ev, Best ) of
        LESS => Best_validated := SOME Validation_ev
      | _ => ()
    end
    else
      (),
    all_indis Population )

fun print_best_validated() = 
  case !Best_validated of
    NONE => output( !std_err, "\nBest validated is NONE\n" )
  | SOME Best => (
  output( !std_err, "\n\nEval value for best validated is\n" );
  eval_value_out( !std_err, Best );
  output( !std_err, "\n" ) )

end (* local *)

val Genealogical_search_count = ref 0.0

fun print_statistics( Population : population ) : unit = (
    output( !std_err, "\n\nGlobal time = " ^ 
      Real.toString(check_timer Global_timer)^"\n");
    print_best_validated();
    output(!std_err, "\n\n" ^ "STATISTICS:\n" ); 
    Compound_trf_synt.print_match_error_statistics();
    Compound_trf_synt.print_time_report();
    
    output( !std_err, 
    "  Genealogical search count = " ^ Real.toString(!Genealogical_search_count) ^ "\n" ^
    "  Extra eval count = " ^ Int.toString( get_eval_count() ) ^ "\n" ^
    "  Simplification count = " ^ Int.toString( get_simplify_count() ) ^ "\n\n" ^
    "  Normal insert count = " ^ Int.toString(!Normal_insert_count) ^ "\n" ^
    "  Would be inserted count = " ^ Int.toString(!Would_be_inserted_count) ^ "\n\n" ^
    "  Current population cardinality with duplicates = " ^ 
       Int.toString(length(all_indis Population )) ^
    "\n" ^
    "  Current population cardinality = " ^ 
       Int.toString(length(hash_make_set(all_indis Population ))) ^
    "\n" ^
    (case length(filter( fn X => 
       !(#max_cost_limit_used X) > 0.01, 
       hash_make_set(all_indis Population )))
    of N =>
    "  No of chosen parents in current population =  " ^ Int.toString N ^ "\n"));
    print_eval_time_report();
    Evaluate.print_PEF_statistics();
    flush_out( !std_err )
    )


val choose_parent = fn Indis =>
  Equalizer.chooseParent(  synt_compl, ! o #max_cost_limit_used, Indis )

fun choose_parents( Indis : individual list, N_parents : int ) 
    : ( individual * real )list =
  if null Indis orelse N_parents = 0 then
    []
  else
  let
    val ( Parent, Cost_limit ) = choose_parent Indis
    val Parent = set_program( Parent, 
      simplify_loop( #program Parent ) )
  in
    if not( used_check( Parent, Cost_limit ) ) then (
(*
      p"\n\n\nIndividual "; p( Id.toString( #individual_id Parent ) );
      p" found to be already used with cost limit ";
      print_real Cost_limit; nl(); nl();
*)
      choose_parents( Indis, N_parents )
      )
    else
      ( Parent, Cost_limit ) :: 
      choose_parents( filter( 
          fn Indi => #individual_id Indi <> #individual_id Parent,
          Indis ),
        N_parents-1 )
  end (* fun choose_parents *)
  


val choose_parents = fn( under_expansion :  individual -> bool,
      Population, N_parents ) =>
  choose_parents( 
    filter( not o under_expansion, screened_all_indis Population ), 
    N_parents )
    

val Expanded_count = ref 0

val choose_parents = 
  fn( under_expansion, Population, N_parents ) =>
let
  val () = update_validation Population
  val () = checkpoint Population
  val Parents = 
    choose_parents( under_expansion, Population, N_parents )
in
  loop( fn ( Parent, Adjusted_cost_limit ) => (
    if real_rep_eq( !(#max_cost_limit_used Parent), 
                    Constants.Initial_cost_limit ) then
      print_individual Parent
    else (
      p"\nExpanding "; p( Id.toString( #individual_id Parent ) ^ " " );
      p( " Adjusted cost limit = "^Real.toString Adjusted_cost_limit  );
      nl(); print_eval_value( #eval_value Parent );
      p"Cutoffs = "; Evaluate.print_cutoffs_list( !(#cutoffs_list Parent) )
      );
    flush_out( !std_out );
    update_sigmas( Parent, Adjusted_cost_limit );
    Total_cost_limit_sum := !Total_cost_limit_sum + Adjusted_cost_limit
    ),
    Parents );

    if !Expanded_count > length(all_indis Population ) then (
      Expanded_count := 0;
      print_statistics Population;
      pop_out( !Trace_stream, Population )
       handle Ex =>  
         output(!std_err,"\n\nWARNING: Cannot print to trace file.\n\n")
      )
    else
      Expanded_count := !Expanded_count + length Parents;
  Parents
end (* val choose_parents *)

val choose_parents = fn X =>
let
  val () = start_timer Choose_parents_timer
  val Y = choose_parents X
  val () = stop_timer Choose_parents_timer
in
  Y
end

fun expand_parent( ( Parent, Adjusted_cost_limit ) : individual * real,
      Population : population ) : population = 
  let
    val () = start_timer Expand_parent_timer
    val () = init_lcss( Population, #ancestor_evals Parent )
    val () = set_initial_idpef_arg( !(#cutoffs_list Parent) )
    val Pop = ref Population
    val Knocked_out = S.empty()

    val N_emitted = ref 0.0
    fun emit(Program,Local_trf_history, Program_eval_value ) =
      let 
        val () = real_inc N_emitted

        val _ = start_timer Genealogical_search_timer
        val _ = start_timer Expand_parent_timer
        val () = start_timer Expand_parent_timer'

        val () = start_timer Petev_timer
        val Eval_value = 
          program_eval_to_eval_value( Program, Program_eval_value )
        val  () = stop_timer Petev_timer

        val () = start_timer Mk_indi_timer

        val Child = mk_indi( Program, Local_trf_history, Eval_value,
                      Parent )
        val () = stop_timer Mk_indi_timer
        val () = stop_timer Expand_parent_timer'
      in
        real_inc Genealogical_search_count;
        Pop := normal_insert( Child, !Pop, Knocked_out );
        stop_timer Genealogical_search_timer;
        stop_timer Expand_parent_timer
      end (* emit *)

    val () = stop_timer Genealogical_search_timer;
    val () = stop_timer Expand_parent_timer;
    val Limit_sum =
      Compound_trf_synt.produce_children( 
        Adjusted_cost_limit, #program Parent,
        !( #last_match_error_cost_limit_sum Parent ), 
        !( #req_match_error_data Parent ), 
        emit )
    val () = start_timer Genealogical_search_timer
    val () = start_timer Expand_parent_timer
    val Population = !Pop
    val () = give_next_req_match_error_data Parent
    val () = end_lcss Population
    val Population = handle_knocked_out( Population, Knocked_out )
  in
    if !N_emitted > 10.0 then 
      #cutoffs_list Parent := next_cutoffs_list()
    else
      ();
    #last_match_error_cost_limit_sum Parent := Limit_sum;
    #max_cost_limit_used Parent := Adjusted_cost_limit;
    store_indi_state Parent;
    stop_timer Expand_parent_timer;
    p(" No of evaluations = "^Real.toString(Evaluate.no_of_evaluations())^"\n");
    Population
  end (* fun expand_parent *)

(* Main loop for the single process version of ADATE. *)
fun main_sp_loop( Population : population ) : unit =
  let
    val [ X as ( Parent, Adjusted_cost_limit ) ] = 
      choose_parents( fn _ => false, Population, 1 )
    val Ti = mk_timer "Temporary expand parent timer"
    val () = start_timer Ti
    val Population = expand_parent( X, Population )
    val T = check_timer Ti / approximate_synt_time_per_exp() * 0.002
    val T = if T <= 0.0 then 1.0e~14 else T
  in
    delete_timer Ti;
    Equalizer.updateConsumption( synt_compl Parent, T );
    nl(); Equalizer.printConsumption(); nl();
    main_sp_loop Population
  end




fun print_pid() = (
  p" Process id = ";
  p( pid() ^"\n" );
  flush_out( !std_out )
  )


(* BEGIN : Code related to the multiprocessing version of ADATE. *)


open MPI_interface

local

fun sync_sym_no( Peer1 : Word32.word, Peer2 : Word32.word ) =
  case sym_no() of ( W1, W2 ) =>
  if list_less( Word32.<, [W1,W2], [Peer1,Peer2] ) then
    set_sym_no( Peer1, Peer2 )
  else
    ()

fun sync_indi_ids( Peer_id : Id.id ) =
  if Id.<( Id.current_id(), Peer_id ) then
    Id.set_id Peer_id
  else 
    ()

in

fun packed_id_info() = case sym_no() of ( W1, W2 ) => pack[
  Word32.toString W1,
  Word32.toString W2,
  Id.id_pack( Id.current_id() )
  ]

fun unpack_id_info( S : string ) : unit = 
let
  val [ W1, W2, Id ] = unpack S
in
  sync_sym_no( word32_from_string W1, word32_from_string W2 );
  sync_indi_ids( Id.id_unpack Id )
end

end (* local *)
  

fun print_indi_ids( Indis : individual list ) : unit =
  loop( fn Indi => 
    p( Id.toString( #individual_id Indi ) ^ " " ),
    Indis )

val EXPAND_TAG = 100000
val RESULT_TAG = 200000

val SERVER = 0


fun send_indis( Indis : individual list, Dest : int, Tag : int ) : unit = (
  send( Int.toString( length Indis ), Dest, Tag );
  loop( fn Indi => send( individual_pack Indi, Dest, Tag ), Indis )
  )

fun receive_indis( Source : int, Tag : int ) : individual list =
let
  val { info, source, tag, ... } =
    receive( Source, Tag )
  val Length = int_from_string info
in
  map( fn _ => case receive( source, Tag ) of { info, ... } =>
    individual_unpack info,
    fromto( 1, Length ) )
end
  

fun send_parent_to_client( 
      Population : population, 
      Seen_indis : S.set, 
      ( Parent, Cost_limit ) : individual * real, 
      Client : int ) : unit =
let
  val Unseen_indis : S.set =
    S.difference( S.list_to_set( all_indis Population ), Seen_indis )
  val Unseen_indis = S.set_to_list Unseen_indis

  val () = (
    p"\nSending parent "; print_indi_ids[ Parent ];
    p"to client "; print_int Client;
    p" with unseen indis = "; print_indi_ids Unseen_indis
    )

in
  send( packed_id_info(), Client, EXPAND_TAG );
  send( real_pack Cost_limit, Client, EXPAND_TAG );
  send_indis( Parent :: Unseen_indis, Client, EXPAND_TAG );
  loop( fn Indi => S.insert( Indi, Seen_indis ), Unseen_indis )
end
  



exception Send_parents_to_clients_exn

structure H = Int_HashTable
exception Client_parent_table_exn
val Client_parent_table : individual H.hash_table = 
  H.mkTable( 10, Client_parent_table_exn )

fun send_parents_to_clients( 
      Population : population, 
      Free_clients : Int_set.set, 
      Seen_indis : S.set vector, 
      Parents : ( individual *  real )list ) : unit =
let
(* Parents may be shorter than Free_clients but never longer. *)
  val Fc = Int_set.set_to_list Free_clients
  val Fc = take( length Parents, Fc )

  val () = 
    if length Fc = length Parents then 
      () 
    else 
      raise Send_parents_to_clients_exn
  val Xs = combine( Parents, Fc )
in
  loop( fn( ( Parent, Cost_limit ), Client ) => (
    send_parent_to_client( 
      Population, 
      Vector.sub( Seen_indis, Client ),
      ( Parent, Cost_limit ),
      Client );
    H.insert Client_parent_table ( Client, Parent );
    Int_set.delete( Client, Free_clients ) ), 
    Xs )
end


exception Receive_children_from_client_exn
fun receive_children_from_some_client( () : unit ) 
    : individual list * real * int =
let
  val { info, source, error, ... } = receive( MPI_ANY_SOURCE, RESULT_TAG )
  val true = error=0
  val () = unpack_id_info info
  val { info, source, error, ... } = receive( source, RESULT_TAG )
  val true = error=0
  val SOME ExpansionTime = Real.fromString info
  val Children = receive_indis( source, RESULT_TAG )
(*
  val () = (
    p"\nReceiving children "; print_indi_ids Children;
    p"from client "; print_int  source
    )
*)
  val Children = map( give_new_id, Children )
in
  ( Children, ExpansionTime, source )
end

fun insert_new_indis( Children, Population ) =
let
  val Pop = ref Population
in
  loop( fn Child => Pop := restored_insert( Child, !Pop ), Children );
  !Pop
end

fun new_seen_indis( Population : population, 
      Seen_indis : S.set vector ) : S.set vector =
let
  val Population = S.list_to_set( all_indis Population )
in
  Vector.map ( fn Seen_indis : S.set =>
    S.list_to_set( filter( fn Indi => S.member( Indi, Population ),
      S.set_to_list Seen_indis ) ) )
    Seen_indis
end
  

exception Server_loop_exn
fun server_loop( 
      Population : population,
      Free_clients : Int_set.set,
      Seen_indis : S.set vector,
      (* Indis in the population that have been "seen" by a given client. *)
      Under_expansion : S.set
      ) : unit =
let
  val Parents : ( individual * real ) list = choose_parents( 
    fn Indi => S.member( Indi, Under_expansion ),
    Population,
    Int_set.H.numItems Free_clients ) 

  val () = loop( fn( Parent, _ ) => S.insert( Parent, Under_expansion ),
             Parents )
(*
  val () = (
    p"\nServer about to send ";
    p(Int.toString(length Parents));
    p" children to clients.";
    flush_out( !std_out )
    )
*)
  val () = 
    send_parents_to_clients( Population, Free_clients, Seen_indis, Parents )

  val ( Updated_parent::Children, ExpansionTime, Client_no ) = 
    receive_children_from_some_client()
  val () =
    assign_indi_state(
      H.lookup Client_parent_table Client_no,
      Updated_parent )
  val () =
    Equalizer.updateConsumption( synt_compl Updated_parent, ExpansionTime );
  val () = ( nl(); Equalizer.printConsumption(); nl() )
  val Population = insert_new_indis( Children, Population )
  val () = if Int_set.member( Client_no, Free_clients ) then 
             raise Server_loop_exn 
           else 
             ()
  val () = Int_set.insert( Client_no, Free_clients )
  val Seen_indis = new_seen_indis( Population, Seen_indis )
  val () = S.delete( H.lookup Client_parent_table Client_no, Under_expansion )
in
  server_loop( Population, Free_clients, Seen_indis, 
    Under_expansion )
end (* fun server_loop *)

val server_loop = fn Population =>
let
  val N = get_comm_size()
in
  server_loop( Population,
    Int_set.list_to_set( fromto( 1, N-1 ) ),
    Vector.fromList( map( fn _ => S.singleton Initial_individual, 
                       fromto( 1, N ) ) ),
    S.empty() )
end

val server_loop = fn X => (
  initialize_approximate_synt_time_per_exp();
  server_loop X )


fun receive_parent_from_server() =
let
  val { info, ... } = receive( SERVER, EXPAND_TAG )
  val () = unpack_id_info info
  val { info, ... } = receive( SERVER, EXPAND_TAG )
  val Cost_limit = real_unpack info
  val Parent :: Unseen_indis = receive_indis( SERVER, EXPAND_TAG )
  val () = (
    p"\nReceiving parent "; print_indi_ids[ Parent ];
    p" from server with unseen indis = "; print_indi_ids Unseen_indis
    )
in
  ( Cost_limit, Parent, map( give_new_id, Unseen_indis ) )
end
  
fun client_loop( Population : population ) : unit =
let
  val () = (
    p"Client "; p(pid());
    p" about to receive_parent_from_server\n";
    flush_out( !std_out )
    )
  val ( Cost_limit, Parent, Unseen_indis ) = receive_parent_from_server()
  val Population = insert_new_indis( Unseen_indis, Population )
  val Old = S.list_to_set( all_indis Population )
  val Ti = mk_timer "Temporary expand parent timer"
  val () = start_timer Ti
  val Population = expand_parent( ( Parent, Cost_limit ), Population )
  val T = check_timer Ti / approximate_synt_time_per_exp() * 0.002
  val T = if T <= 0.0 then 1.0e~14 else T
  val () = delete_timer Ti
  val Children = S.difference( S.list_to_set( all_indis Population ), Old )
  val Children = S.set_to_list Children
  val () = (
    p"\nSending children "; print_indi_ids Children;
    p"to server from client with pid ";
    p( pid() ^"\n" ); flush_out( !std_out )
    )
in
  send( packed_id_info(), SERVER, RESULT_TAG );
  send( Real.toString T, SERVER, RESULT_TAG );
  send_indis( Parent::Children, SERVER, RESULT_TAG );
  client_loop Population
end

val client_loop = fn X => (
  initialize_approximate_synt_time_per_exp();
  client_loop X )

exception Mpi_start_exn
fun mpi_start() = 
let
  val () = init()
  val () = C_interface.GCmessages false
  val () = Evaluate.reinitialize Spec.Spec_file_name;
  val Rank = get_comm_rank()
in
  start_timer Global_timer;
  start_timer Genealogical_search_timer;
  if Rank < 0 then
    raise Mpi_start_exn
  else if Rank > 0 then
    case "." of Check_point_dir =>
    case Spec_name ^ ".clienttrace." ^Int.toString Rank ^ "." ^ pid() of Trace_file =>
    case Spec_name ^ ".clientlog." ^ Int.toString Rank ^ "." ^pid() of Log_file =>
  (
    std_err := TextIO.stdErr;
    std_out := TextIO.stdOut;
    Check_point_directory := Check_point_dir;
    p"\nA client has ";
    print_pid();
    client_loop Initial_population
    )
  else
  case "." of Check_point_dir =>
  case Spec_name ^ ".trace." ^ pid() of Trace_file =>
  case Spec_name ^ ".log." ^ pid() of Log_file =>
(
  Trace_file_name := Trace_file;
  Log_file_name := Log_file;
  std_err := TextIO.openOut Trace_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Trace_file ^
        "\n\n" );
      raise Ex
      );
  std_out := TextIO.openOut Log_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Log_file ^
        "\n\n" );
      raise Ex
      );
  Check_point_directory := Check_point_dir;
  p"\nThe server has ";
  print_pid();
  server_loop Initial_population
  )
end (* fun mpi_start *)

(* END : Code related to the multiprocessing version of ADATE. *)


fun start() = 
  case "." of Check_point_dir =>
  case Spec_name ^ ".trace." ^ pid() of Trace_file =>
  case Spec_name ^ ".log." ^ pid() of Log_file =>
(
  Trace_file_name := Trace_file;
  Log_file_name := Log_file;
  std_err := TextIO.openOut Trace_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Trace_file ^
        "\n\n" );
      raise Ex
      );
  std_out := TextIO.openOut Log_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Log_file ^
        "\n\n" );
      raise Ex
      );
  Check_point_directory := Check_point_dir;
  start_timer Global_timer;
  start_timer Genealogical_search_timer;
  print_pid();
  main_sp_loop Initial_population
  )

fun restart() = 
  case "." of Check_point_dir =>
  case Spec_name ^ ".trace." ^ pid() of Trace_file =>
  case Spec_name ^ ".log." ^ pid() of Log_file =>
  case Spec_name ^ ".0.pop" of Pop_file =>
(
  Trace_file_name := Trace_file;
  Log_file_name := Log_file;
  std_err := TextIO.openAppend Trace_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Trace_file ^
        "\n\n" );
      raise Ex
      );
  std_out := TextIO.openAppend Log_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Log_file ^
        "\n\n" );
      raise Ex
      );
  Check_point_directory := Check_point_dir;
  start_timer Global_timer;
  start_timer Genealogical_search_timer;
  case restore Pop_file of ( Gen, Glo, Consumption, Population ) => (
    output(!std_out,"\n\nRESUMING EXECUTION\n");
    print_best_list();
    output( !std_out,
"\n\n===========================================================================\n\n\n");
    set_timer(Global_timer,Glo);
    set_timer(Genealogical_search_timer,Gen);
    Equalizer.setConsumption Consumption;
    Expanded_count := Max_int;
    refresh_save_info();
    print_pid();
    main_sp_loop( Population )
  ) )
  handle Ex => re_raise( Ex, "restart" )


fun mpi_restart() = 
let
  val Population =
  case "." of Check_point_dir =>
  case Spec_name ^ ".trace." ^ pid() of Trace_file =>
  case Spec_name ^ ".log." ^ pid() of Log_file =>
  case Spec_name ^ ".0.pop" of Pop_file =>
(
  Trace_file_name := Trace_file;
  Log_file_name := Log_file;
  std_err := TextIO.openAppend Trace_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Trace_file ^
        "\n\n" );
      raise Ex
      );
  std_out := TextIO.openAppend Log_file 
    handle Ex => (
      output( TextIO.stdErr, "\n\nERROR: Cannot open file " ^ Log_file ^
        "\n\n" );
      raise Ex
      );
  Check_point_directory := Check_point_dir;
  start_timer Global_timer;
  start_timer Genealogical_search_timer;
  case restore Pop_file of ( Gen, Glo, Consumption, Population ) => (
    output(!std_out,"\n\nRESUMING EXECUTION\n");
    print_best_list();
    output( !std_out,
"\n\n===========================================================================\n\n\n");
    set_timer(Global_timer,Glo);
    set_timer(Genealogical_search_timer,Gen);
    Equalizer.setConsumption Consumption;
    Expanded_count := Max_int;
    refresh_save_info();
    print_pid();
    Population
  ) )
  handle Ex => re_raise( Ex, "mpi_restart" )

  val () = init()
  val () = C_interface.GCmessages false
  val () = Evaluate.reinitialize Spec.Spec_file_name;
  val Rank = get_comm_rank()
in
  if Rank < 0 then
    raise Mpi_start_exn
  else if Rank > 0 then (
    std_err := TextIO.stdErr;
    std_out := TextIO.stdOut;
    p"\n"; print_pid();
    client_loop Population
    )
  else (
  print_pid();
  server_loop Population
  )
end (* fun mpi_start *)


fun export() = (
  prepare_timers_for_export();
  SMLofNJ.exportFn( "atmpi", fn _ => 
    ( recover_timers_from_export();
      Evaluate.reinitialize Spec.Spec_file_name;
      mpi_start(); 
      OS.Process.success ) 
      ) )



fun export_restart() = (
  prepare_timers_for_export();
  SMLofNJ.exportFn( "armpi", fn _ => 
    ( recover_timers_from_export();
      Evaluate.reinitialize Spec.Spec_file_name;
      mpi_restart(); 
      OS.Process.success ) 
      ) )




end (* functor G_functor *)
