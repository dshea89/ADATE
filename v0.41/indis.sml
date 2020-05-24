(*
  File: indis.sml
  Created: 1997-03-27.
  Modified: 2001-02-09.
*)

signature INDIS =
sig

val Global_timer : Lib.timer

structure Evaluate : EVALUATE

datatype indi_category = time_class | lcs_class | scm_class | out_class | base

type trace_info = { base_id : Id.id, class : indi_category } option

type old_individual = { 
  individual_id : Id.id, 
  trace_info : trace_info,
  ancestor_ids : Id.id list, 
  ancestor_evals : Evaluate.quick_eval_value_type list,
  max_cost_limit_used : real ref, 
  last_match_error_cost_limit_sum : real ref,
  req_match_error_data : REQ_lib.req_match_error_data ref,
  eval_value : Evaluate.eval_value_type,
  program : Ast.dec,
  local_trf_history : Ast_lib2.atomic_trf_record list, 
  creation_time : real }

type individual = { 
  individual_id : Id.id, 
  trace_info : trace_info,
  ancestor_ids : Id.id list, 
  ancestor_evals : Evaluate.quick_eval_value_type list,
  max_cost_limit_used : real ref, 
  last_match_error_cost_limit_sum : real ref,
  req_match_error_data : REQ_lib.req_match_error_data ref,
  is_new : bool ref,
(* To be used for parallization. Indicates that an individual has been
   added to the population since the fork and should be sent back
   to the master process.
*)
  cutoffs_list : Evaluate.quick_eval_value_type list option list ref,
  eval_value : Evaluate.eval_value_type,
  validation_eval_value : Evaluate.eval_value_type option ref,
  program : Ast.dec,
  local_trf_history : Ast_lib2.atomic_trf_record list, 
  creation_time : real }
val individual_pack : individual -> string
val individual_unpack : string -> individual
val indi_save : TextIO.outstream * individual -> unit
val indi_restore : Ast.symbol Ast.Symbol_HashTable.hash_table * 
  TextIO.instream -> individual
(*
val old_indi_restore : Ast.symbol Ast.Symbol_HashTable.hash_table * 
  TextIO.instream -> individual
*)
val mk_indi : Ast.dec * Ast_lib2.atomic_trf_record list *
  Evaluate.eval_value_type * individual -> individual

val indi_out : TextIO.outstream * individual -> unit
val give_new_id : individual -> individual
val give_next_req_match_error_data : individual -> unit
val print_individual : individual -> unit
val Initial_individual : individual

val set_program : individual * Ast.dec -> individual
val set_trace_info : individual * trace_info -> individual
val set_ancestor_evals : individual * 
  Evaluate.quick_eval_value_type list -> individual

val assign_indi_state : individual * individual -> unit

val Syntactic_complexity_selectors : 
  ( Evaluate.eval_value_type -> real ) list

val best_update : individual -> unit
val print_best_list : unit -> unit

val hash_make_set : individual list -> individual list
structure Individual_set : HASH_SET

val reevaluate : individual -> individual

end (* signature INDIS *)


functor Indis_functor( structure Synt_lib : SYNT_LIB ) : INDIS =
struct
open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib4 Print Synt_lib.Evaluate

structure Evaluate = Synt_lib.Evaluate

val Global_timer = mk_timer("indis.sml:Global_timer")

datatype indi_category = time_class | lcs_class | scm_class | out_class | base
type trace_info = { base_id : Id.id, class : indi_category } option

fun indi_category_to_string X =
  case X of time_class => "time" | lcs_class => "lcs" 
  | scm_class => "scm" | out_class => "out" | base => "base"

val indi_category_pack = indi_category_to_string

fun indi_category_unpack( S : string ) : indi_category =
  case S of "time" => time_class | "lcs" => lcs_class
  | "scm" => scm_class | "out" => out_class | "base" => base


fun trace_info_to_string( T : trace_info ) : string =
  case T of 
    NONE => ""
  | SOME{ base_id, class } => 
      indi_category_to_string class ^ " for " ^ Id.toString base_id

fun trace_info_pack( TI : trace_info ) : string =
  option_pack( fn{ base_id, class } =>
    pack[
      Id.id_pack base_id,
      indi_category_pack class 
      ],
    TI )

fun trace_info_unpack( S : string ) : trace_info =
  option_unpack( fn S =>
    case unpack S of [ B, C ] => {
      base_id = Id.id_unpack B,
      class = indi_category_unpack C
      },
    S )
    


type old_individual = { 
  individual_id : Id.id, 
  trace_info : trace_info,
  ancestor_ids : Id.id list, 
  ancestor_evals : Evaluate.quick_eval_value_type list,
  max_cost_limit_used : real ref, 
  last_match_error_cost_limit_sum : real ref,
  req_match_error_data : REQ_lib.req_match_error_data ref,
  eval_value : Evaluate.eval_value_type,
  program : Ast.dec,
  local_trf_history : Ast_lib2.atomic_trf_record list, 
  creation_time : real }

type individual = { 
  individual_id : Id.id, 
  trace_info : trace_info,
  ancestor_ids : Id.id list, 
  ancestor_evals : Evaluate.quick_eval_value_type list,
  max_cost_limit_used : real ref, 
  last_match_error_cost_limit_sum : real ref,
  req_match_error_data : REQ_lib.req_match_error_data ref,
  is_new : bool ref,
  cutoffs_list : Evaluate.quick_eval_value_type list option list ref,
  eval_value : Evaluate.eval_value_type,
  validation_eval_value : Evaluate.eval_value_type option ref,
  program : Ast.dec,
  local_trf_history : Ast_lib2.atomic_trf_record list, 
  creation_time : real }


fun individual_pack( { individual_id, trace_info, ancestor_ids, ancestor_evals,
        max_cost_limit_used, last_match_error_cost_limit_sum, 
        req_match_error_data, is_new, cutoffs_list,
        eval_value, validation_eval_value, program, 
        local_trf_history, creation_time} : individual )
    : string =
  pack[
    Id.id_pack individual_id, 
    trace_info_pack trace_info, 
    list_pack( Id.id_pack, ancestor_ids ), 
    list_pack( quick_eval_value_type_pack, ancestor_evals ),
    real_pack( !max_cost_limit_used ), 
    real_pack( !last_match_error_cost_limit_sum ), 
    REQ_lib.req_match_error_data_pack( !req_match_error_data ), 
    Bool.toString( !is_new ), 
    list_pack( fn X => 
      option_pack( fn Ys => list_pack( quick_eval_value_type_pack, Ys ), X ),
      !cutoffs_list ),
     eval_value_type_pack eval_value, 
     option_pack( eval_value_type_pack, !validation_eval_value ), 
     dec_pack program, 
     list_pack( atomic_trf_record_pack, 
       map( make_blastable, local_trf_history ) ), 
     real_pack creation_time
     ]



fun individual_unpack( S : string ) : individual = (
  case unpack S of 
    [ ID, TI, AID, AE, MC, LM, RMD, IN, CL, EV, VEV, P, LT, CT ] => { 
      individual_id = Id.id_unpack ID
        handle Ex => re_raise( Ex, "individual_unpack:1" ), 
      trace_info = trace_info_unpack TI
        handle Ex => re_raise( Ex, "individual_unpack:2" ), 
      ancestor_ids = list_unpack( Id.id_unpack, AID )
        handle Ex => re_raise( Ex, "individual_unpack:3" ), 
      ancestor_evals = list_unpack( quick_eval_value_type_unpack, AE )
        handle Ex => re_raise( Ex, "individual_unpack:4" ),
      max_cost_limit_used = ref( real_unpack MC )
        handle Ex => re_raise( Ex, "individual_unpack:5" ), 
      last_match_error_cost_limit_sum = ref( real_unpack LM )
        handle Ex => re_raise( Ex, "individual_unpack:6" ), 
      req_match_error_data = ref( REQ_lib.req_match_error_data_unpack RMD )
        handle Ex => re_raise( Ex, "individual_unpack:7" ),
      is_new = ref( bool_from_string IN )
        handle Ex => re_raise( Ex, "individual_unpack:8" ), 
      cutoffs_list = ref( list_unpack( fn S1 =>
        option_unpack( fn S2 => 
          list_unpack( quick_eval_value_type_unpack, S2 ),
          S1 ),
        CL  ) )
        handle Ex => re_raise( Ex, "individual_unpack:9" ),
      eval_value = eval_value_type_unpack EV, 
      validation_eval_value = 
        ref( option_unpack( eval_value_type_unpack, VEV ) )
        handle Ex => re_raise( Ex, "individual_unpack:10" ),
      program = dec_unpack P
        handle Ex => re_raise( Ex, "individual_unpack:11" ), 
      local_trf_history = list_unpack( atomic_trf_record_unpack, LT )
        handle Ex => re_raise( Ex, "individual_unpack:12" ), 
      creation_time = real_unpack CT
        handle Ex => re_raise( Ex, "individual_unpack:13" )
      } )
  handle Ex => re_raise( Ex, "individual_unpack" )









exception Give_new_id
fun give_new_id({individual_id, trace_info, ancestor_ids, ancestor_evals,
        last_match_error_cost_limit_sum, req_match_error_data,
        is_new, cutoffs_list,
        max_cost_limit_used, eval_value, validation_eval_value, program, 
        local_trf_history, creation_time} : individual )
    : individual =
  if hd ancestor_ids <> individual_id then
    raise Give_new_id
  else
  let
    val Id = Id.gen_id()
  in
  { individual_id=Id, trace_info = trace_info,
    ancestor_ids = Id :: tl ancestor_ids,
    last_match_error_cost_limit_sum=ref(!last_match_error_cost_limit_sum),
    req_match_error_data = ref( !req_match_error_data ),
    is_new = ref( !is_new ),
    cutoffs_list = ref( !cutoffs_list ),
    ancestor_evals=ancestor_evals,
    eval_value=eval_value, validation_eval_value = validation_eval_value, 
    program=program, 
    local_trf_history=local_trf_history, creation_time=creation_time,
    max_cost_limit_used=ref(!max_cost_limit_used) }
  end

fun give_next_req_match_error_data( Indi : individual ) : unit =
  #req_match_error_data Indi :=
    REQ_lib.next_req_match_error_data( !(#req_match_error_data Indi) )

fun set_eval_value({individual_id, trace_info, ancestor_ids, ancestor_evals,
        validation_eval_value,
        last_match_error_cost_limit_sum, req_match_error_data,
        is_new, cutoffs_list,
        max_cost_limit_used, program, 
        local_trf_history, creation_time, ...} : individual,
      New_value : eval_value_type ) : individual =
    
  { individual_id=individual_id, trace_info = trace_info,
    ancestor_ids=ancestor_ids,
    last_match_error_cost_limit_sum=last_match_error_cost_limit_sum,
    req_match_error_data = req_match_error_data,
    is_new =  is_new,
    cutoffs_list = cutoffs_list,
    ancestor_evals = normal_to_quick New_value :: tl ancestor_evals,
    eval_value=New_value, validation_eval_value = validation_eval_value,
    program=program, 
    local_trf_history=local_trf_history, creation_time=creation_time,
    max_cost_limit_used=max_cost_limit_used }
    


fun set_trace_info({individual_id, eval_value, 
        validation_eval_value,
        ancestor_ids, ancestor_evals,
        last_match_error_cost_limit_sum, req_match_error_data,
        is_new, cutoffs_list,
        max_cost_limit_used, program, 
        local_trf_history, creation_time, ...} : individual,
      Trace_info : trace_info ) : individual =
    
  { individual_id=individual_id, trace_info = Trace_info,
    ancestor_ids=ancestor_ids,
    last_match_error_cost_limit_sum=last_match_error_cost_limit_sum,
    req_match_error_data = req_match_error_data,
    is_new = is_new, cutoffs_list = cutoffs_list,
    ancestor_evals=ancestor_evals,
    eval_value=eval_value, validation_eval_value = validation_eval_value,
    program=program, 
    local_trf_history=local_trf_history, creation_time=creation_time,
    max_cost_limit_used=max_cost_limit_used }
    


fun set_program({individual_id, trace_info, ancestor_ids, ancestor_evals,
        last_match_error_cost_limit_sum, req_match_error_data,
        is_new, cutoffs_list,
        max_cost_limit_used,
        eval_value, validation_eval_value,
        local_trf_history,
        creation_time,  ...} : individual,
      Program ) : individual =
  { individual_id=individual_id,trace_info = trace_info,
    ancestor_ids=ancestor_ids,
    last_match_error_cost_limit_sum=last_match_error_cost_limit_sum,
    req_match_error_data = req_match_error_data,
    is_new = is_new, cutoffs_list = cutoffs_list,
    ancestor_evals=ancestor_evals, 
    eval_value=eval_value, validation_eval_value = validation_eval_value,
    program=Program, 
    local_trf_history=local_trf_history, creation_time=creation_time,
    max_cost_limit_used=max_cost_limit_used }


fun set_ancestor_evals({individual_id, trace_info, ancestor_ids,
        last_match_error_cost_limit_sum, req_match_error_data,
        is_new, cutoffs_list,
        max_cost_limit_used,
        eval_value, validation_eval_value,
        program, local_trf_history,
        creation_time,  ...} : individual,
      Anc_evals ) : individual =
  { individual_id=individual_id, trace_info = trace_info,
    ancestor_ids=ancestor_ids,
    last_match_error_cost_limit_sum=last_match_error_cost_limit_sum,
    req_match_error_data = req_match_error_data,
    is_new = is_new, cutoffs_list = cutoffs_list,
    ancestor_evals=Anc_evals, 
    eval_value=eval_value, validation_eval_value = validation_eval_value,
    program=program, 
    local_trf_history=local_trf_history, creation_time=creation_time,
    max_cost_limit_used=max_cost_limit_used }
    



fun set_local_trf_history({individual_id, trace_info, ancestor_ids,
        last_match_error_cost_limit_sum, req_match_error_data,
        is_new, cutoffs_list,
        max_cost_limit_used,
        eval_value, validation_eval_value,
        program, 
        creation_time,  ancestor_evals, ... } : individual,
      Local_trf_history ) : individual =
  { individual_id=individual_id, trace_info = trace_info,
    ancestor_ids=ancestor_ids,
    last_match_error_cost_limit_sum=last_match_error_cost_limit_sum,
    req_match_error_data = req_match_error_data,
    is_new = is_new, cutoffs_list = cutoffs_list,
    ancestor_evals=ancestor_evals, 
    eval_value=eval_value, validation_eval_value = validation_eval_value,
    program=program, 
    local_trf_history=Local_trf_history, creation_time=creation_time,
    max_cost_limit_used=max_cost_limit_used }

exception Assign_indi_state_exn 
fun assign_indi_state( To : individual,
  {individual_id, trace_info, ancestor_ids, ancestor_evals,
        last_match_error_cost_limit_sum, req_match_error_data,
        is_new, cutoffs_list,
        max_cost_limit_used,
        eval_value, validation_eval_value,
        local_trf_history,
        creation_time,  ...} : individual ) : unit = (
(*
  if #individual_id To <> individual_id then 
    raise Assign_indi_state_exn 
  else 
    ();
*)
  #max_cost_limit_used To := !max_cost_limit_used;
  #last_match_error_cost_limit_sum To := !last_match_error_cost_limit_sum;
  #req_match_error_data To := !req_match_error_data;
  #cutoffs_list To := !cutoffs_list
  )
  


    
(*
fun old_to_new_indi({individual_id, trace_info, ancestor_ids, ancestor_evals,
        last_match_error_cost_limit_sum, req_match_error_data,
        max_cost_limit_used, eval_value, program, 
        local_trf_history, creation_time} : old_individual )
    : individual =
(* Only used when changing representation of an individual to convert
   populations saved with the old representation. *)

  { individual_id=individual_id, trace_info = trace_info,
    ancestor_ids = ancestor_ids,
    last_match_error_cost_limit_sum=ref(!last_match_error_cost_limit_sum),
    req_match_error_data = ref( !req_match_error_data ),
    is_new = ref false,
    cutoffs_list = ref( Evaluate.First_cutoffs_list ),
    ancestor_evals=ancestor_evals,
    eval_value=eval_value, 
    validation_eval_value = ref NONE,
    program=program, 
    local_trf_history=local_trf_history, creation_time=creation_time,
    max_cost_limit_used=ref(!max_cost_limit_used) }
*)



fun print_individual({individual_id, trace_info, ancestor_ids, ancestor_evals,
       max_cost_limit_used, cutoffs_list, eval_value,
      validation_eval_value, program,
      local_trf_history, creation_time,...} : individual) =
  let fun p S = output(!std_out,S)
      fun q Id_no = p(Id.toString Id_no)
  in
    p "\n----------------------------------------------------------------------";
    p("\nIndividual id = " ^ Id.toString individual_id);
    p("  Trace info = " ^ trace_info_to_string trace_info );
    p "\n\nAncestor ids = "; print_list(q,ancestor_ids);
    p "\n\nAncestor evals = "; 
      print_list(print_quick_eval_value,ancestor_evals);
    p( "\n\nMax cost limit used = "^Real.toString(!max_cost_limit_used));
(*
    p"\n\nCutoffs list = \n"; Evaluate.print_cutoffs_list( !cutoffs_list );
*)
    p( "\n\nEval fun value =\n "); print_eval_value eval_value;
    ( case !validation_eval_value of
        NONE => ()
      | SOME VE => (
          p( "\nValidation eval fun value =\n "); print_eval_value VE ) );
   nl(); print_dec' program;
   p "\n\nLocal trf history = "; print_trf_history(rev local_trf_history); 
    p("\nCreation time = " ^ Real.toString creation_time);
    flush_out( !std_out )
  end


exception Indi_out_exn
fun indi_out( out : outstream, { individual_id,
      trace_info, ancestor_ids, ancestor_evals,
      eval_value, ... } : individual ) : unit =
  let 
    fun p S = output(out,S)
     
    val Id_string =
      case trace_info of
        NONE => ""
      | SOME{ base_id, class }  => 
      case class of
        base => if base_id <> individual_id then raise Indi_out_exn else
          " " ^ Id.toString base_id
      | _ => ""
  in
(*
    list_out( out, fn(out, Id_no ) => 
        output( out, Id.toString Id_no ), 
      ancestor_ids);
    p "\n";
    list_out(out,quick_eval_value_out,ancestor_evals); p Id_string;
    p "\n";
*)
    (case Id_string of "" => () | _ => p Id_string; p"\n" );
    eval_value_out(out, eval_value);
    flush_out out
  end


val Initial_program = 
  case Evaluate.Spec.Initial_program of
    NONE => Predefined.initial_program()
  | SOME S => Predefined.mk_f_dec S

val Initial_program = Synt_lib.simplify_loop Initial_program

val _ = ( output(!std_out,"\n\nThe initial program is\n");
  print_dec Initial_program )

val _ = let fun loop() =
  if Evaluate.cum_eval_time() > 1.0E~49 then () else (
    Evaluate.program_eval_fun_max Initial_program;
    loop() )
  in
    loop()
  end


val Initial_individual : individual = 
  let
    val { 
        n_c_n_w_n_o = (N_c,N_w,N_o), 
        n_c', entropy,
        extra_quality,
        call_count, time_complexity,
        fingerprint,
        no_globals,  ... } : Evaluate.program_eval_type = 
      Evaluate.program_eval_fun_max Initial_program
    val S = Evaluate.syntactic_complexities( Initial_program, no_globals )
    val SF = Evaluate.syntactic_fingerprint Initial_program
    val Eval_value : eval_value_type = 
      { 
        n_c = N_c, n_w = N_w, n_o = N_o, extra_quality = extra_quality,
        n_c' = n_c', entropy = entropy,
        syntactic_fingerprint = SF,
        call_count = call_count, time_complexity = time_complexity,
        fingerprint = fingerprint,
        syntactic_complexities = S }
    val Id = Id.gen_id()
  in
    { individual_id=Id,
      trace_info = NONE,
      ancestor_ids=[Id], 
      ancestor_evals = [ normal_to_quick Eval_value ],
      last_match_error_cost_limit_sum = ref 0.0, 
      req_match_error_data = ref( REQ_lib.initial_req_match_error_data() ),
      is_new = ref false,
      cutoffs_list = ref Evaluate.First_cutoffs_list,
      max_cost_limit_used = ref 0.0, 
      eval_value=Eval_value, 
      validation_eval_value = ref NONE,
      program=Initial_program, 
      local_trf_history=nil, creation_time=check_timer Global_timer }
  end


(*
val Old_initial_individual : old_individual = 
  let
    val { 
        n_c_n_w_n_o = (N_c,N_w,N_o), 
        n_c', entropy,
        extra_quality,
        call_count, time_complexity,
        fingerprint,
        no_globals,  ... } : Evaluate.program_eval_type = 
      Evaluate.program_eval_fun_max Initial_program
    val S = Evaluate.syntactic_complexities( Initial_program, no_globals )
    val SF = Evaluate.syntactic_fingerprint Initial_program
    val Eval_value : eval_value_type = 
      { 
        n_c = N_c, n_w = N_w, n_o = N_o, extra_quality = extra_quality,
        n_c' = n_c', entropy = entropy,
        syntactic_fingerprint = SF,
        call_count = call_count, time_complexity = time_complexity,
        fingerprint = fingerprint,
        syntactic_complexities = S }
    val Id = Id.gen_id()
  in
    { individual_id=Id,
      trace_info = NONE,
      ancestor_ids=[Id], 
      ancestor_evals = [ normal_to_quick Eval_value ],
      last_match_error_cost_limit_sum = ref 0.0, 
      req_match_error_data = ref( REQ_lib.initial_req_match_error_data() ),
      max_cost_limit_used = ref 0.0, 
      eval_value=Eval_value, 
      program=Initial_program, 
      local_trf_history=nil, creation_time=check_timer Global_timer }
  end
*)


fun indi_save( out : outstream, X : individual ) =
  let
    fun p S = output( out, S )
    val X = set_local_trf_history( X,
      map( make_blastable, #local_trf_history X ) )
    val S = individual_pack X
  in
    p( Int.toString( String.size S ) ); p"\n";
    p S
  end
  handle Ex => re_raise( Ex, "indi_save" )

fun reevaluate( Indi as { program, ... } : individual ) =
  let
    val Program_eval_value as { call_count, time_complexity,
          fingerprint, no_globals, ... } =
      program_eval_fun_max program
    val Quick : quick_eval_value_type =
      program_eval_type_to_quick Program_eval_value
    val S = syntactic_complexities( program, no_globals )
    val SF = syntactic_fingerprint program
    val Eval_value = 
      quick_to_normal( Quick, S, SF, call_count, time_complexity, fingerprint )
  in
    set_eval_value( Indi, Eval_value )
  end

local

structure H = Symbol_HashTable

fun apply_to_ty_exp( ty_con_exp( Sym, TEs ), Sym_mapping ) =
let
  val Sym =
    case H.find Sym_mapping Sym of
      NONE => Sym
    | SOME Sym => Sym
in
  ty_con_exp( Sym, map( fn TE => apply_to_ty_exp( TE, Sym_mapping ), TEs ) )
end

in (* local *)


fun apply_ty_sym_subst( D : dec, Sym_mapping : symbol H.hash_table ) : dec =
  info_map_dec( 
    fn TE => apply_to_ty_exp( TE, Sym_mapping ),
    fn{ schematic_vars=[], ty_exp=TE } =>
      { schematic_vars=[], ty_exp = apply_to_ty_exp( TE, Sym_mapping ) },
    D )

end (* local *)

fun only_NONE_cutoffs( Indi : individual ) : bool =
  case !( #cutoffs_list Indi ) of Xs =>
    not( null Xs ) andalso forall( is_NONE, Xs )


fun indi_restore( Sym_mapping, instream : TextIO.instream ) : individual =
  let
    fun inputLine() = TextIO.inputLine instream
    fun inputN N = TextIO.inputN( instream, N )
    val N = case Int.fromString( inputLine() ) of SOME X => X
    val Str = inputN N
    val Indi : individual = individual_unpack Str
    val Indi = set_local_trf_history( Indi,
      map( unmake_blastable, #local_trf_history Indi ) )
(*
    val () = 
      if Id.toString( #individual_id Indi ) = "0_c81e2c" then (
        p"\n\nWANTED INDI IS:\n";
        print_individual Indi
        )
      else
        ()
*)
    val D =  
      apply_ty_sym_subst( 
        apply_sym_subst( #program Indi, Sym_mapping ),
        Sym_mapping ) 
  in
    if only_NONE_cutoffs Indi then #max_cost_limit_used Indi := 100.0 else ();
    reevaluate( set_program( Indi, D ) )
  end
  handle Ex => re_raise( Ex, "indi_restore" )

(*
fun old_indi_restore( Sym_mapping, instream : TextIO.instream ) : individual =
  let
    fun inputLine() = TextIO.inputLine instream
    fun inputN N = TextIO.inputN( instream, N )
    val N = case Int.fromString( inputLine() ) of SOME X => X
    val Str = inputN N
    val Indi : old_individual = 
      C_interface.blastRead( Byte.stringToBytes Str, Old_initial_individual )
    val Indi = old_to_new_indi Indi
    val Indi = set_local_trf_history( Indi,
      map( unmake_blastable, #local_trf_history Indi ) )
(*
    val () = 
      if Id.toString( #individual_id Indi ) = "0_c81e2c" then (
        p"\n\nWANTED INDI IS:\n";
        print_individual Indi
        )
      else
        ()
*)
    val D =  
      apply_ty_sym_subst( 
        apply_sym_subst( #program Indi, Sym_mapping ),
        Sym_mapping ) 
  in
    reevaluate( set_program( Indi, D ) )
  end
*)



fun mk_indi( Program, Local_trf_history, Eval_value, 
      Parent as {ancestor_ids, ancestor_evals, ... } : individual )
    : individual =
  let 
    val Id = Id.gen_id()
  in
    { 
    ancestor_ids = take( 10, Id::ancestor_ids ),
    ancestor_evals = take( 10, normal_to_quick Eval_value :: ancestor_evals ),
    max_cost_limit_used = ref 0.0, 
    last_match_error_cost_limit_sum = ref 0.0, 
    req_match_error_data = ref( REQ_lib.initial_req_match_error_data() ),
    is_new = ref false,
    cutoffs_list = ref Evaluate.First_cutoffs_list,
    eval_value = Eval_value, validation_eval_value = ref NONE,
    program=Program, local_trf_history = Local_trf_history,
    individual_id=Id, trace_info = NONE,
    creation_time = check_timer Global_timer }
  end


val Syntactic_complexity_selectors : (eval_value_type ->  real) list = 
  [ fn X => hd(#syntactic_complexities X),
    fn X => hd(tl(#syntactic_complexities X)) ]

local

fun real_list_less(nil,nil) = false
  | real_list_less(X::Xs,Y::Ys) =
  if real_eq(X,Y) then
    real_list_less(Xs,Ys) 
  else
    X<Y

fun real_list_eq(nil,nil) = true
  | real_list_eq(X::Xs,Y::Ys) = real_eq(X,Y) andalso real_list_eq(Xs,Ys)

type best_type = {syntactic_complexity : real, time_complexity:real,
  individual:individual}

val Best_list : best_type list ref = 
  ref( {syntactic_complexity = 0.0, time_complexity = 0.0,
    individual = Initial_individual} :: nil )


val Best_quick = ref( normal_to_quick(#eval_value Initial_individual))

fun best_list_prune1( Min_time_complexity, Xs : best_type list ) =
  case Xs of
    nil => nil
  | X1::Xs1 => 
      if #time_complexity  X1 < Min_time_complexity then
        X1 :: best_list_prune1( #time_complexity X1, Xs1 )
      else
        best_list_prune1( Min_time_complexity, Xs1 )

fun best_list_prune( X1 :: Xs1 : best_type list ) = 
  X1 :: best_list_prune1( #time_complexity X1, Xs1 )

(* open Signals *)
  
val Best_individual = ref Initial_individual
val Best_individual' = ref Initial_individual

fun is_better_than_best( Eval_value : eval_value_type ) : bool =
  case pe5_cmp( Eval_value, #eval_value(!Best_individual) ) of
    LESS => true
  | _ => false

fun is_better_than_best'( Eval_value : eval_value_type ) : bool =
  case pe4_cmp( Eval_value, #eval_value(!Best_individual') ) of
    LESS => true
  | _ => false

in (* local *)

fun best_update( Indi : individual )
    : unit = 
  case #eval_value Indi of Eval_value => (
  if is_better_than_best Eval_value then 
    Best_individual := Indi
  else
    ();
  if is_better_than_best' Eval_value then
    Best_individual' := Indi
  else
    ();
  let 
    val Quick = normal_to_quick Eval_value
    val new_best_elem = fn () =>
      { syntactic_complexity = 
          (hd Syntactic_complexity_selectors) Eval_value,
        time_complexity = #time_complexity Eval_value,
        individual = Indi } 
  in
  case quick_pe5_cmp( !Best_quick, Quick ) of
    LESS => ()
  | GREATER => (
    Best_quick := Quick;
    Best_list := new_best_elem() ::nil )
  | EQUAL =>
    if member'(
      fn( {syntactic_complexity=S1,time_complexity=T1,...}, 
          {syntactic_complexity=S2,time_complexity=T2,...} ) =>
        real_list_eq( [S1,T1], [S2,T2] ),
      new_best_elem(),
      !Best_list ) 
    then  
      () 
    else
      Best_list := best_list_prune( list_insert(
        fn( {syntactic_complexity=S1,time_complexity=T1,...}, 
            {syntactic_complexity=S2,time_complexity=T2,...} ) =>
          real_list_less( [S1,T1], [S2,T2] ),
      new_best_elem(),
      !Best_list ) )
  end )     


fun print_best_list() = (
  output(!std_out,"\n\n\nTHE BEST INDIVIDUALS FOUND SO FAR ARE\n");
  map( print_individual o #individual, !Best_list ); () )

(*
fun sig_handler(N : int, C : unit cont) : unit cont =
  ( print_best_list(); print_eval_time_report(); C )

fun sig_handler2(N : int, C : unit cont) : unit cont =
  ( print_eval_time_report(); 
   C )
val _ = maskSignals false
val _ = setHandler( SIGUSR1, SOME sig_handler ) 
val _ = setHandler( SIGUSR2, SOME sig_handler2 ) 
*)
end (* local *)

local

structure Individual_hash_key =
  struct
    type hash_key = individual
    fun hashVal( X : individual ) = Id.hashVal( #individual_id X )
    fun sameKey( X : individual, Y : individual ) = 
      #individual_id X = #individual_id Y
  end 

structure H = HashTableFn( Individual_hash_key )

structure G = Hash_make_set_functor( H )

in


val hash_make_set = G.hash_make_set

structure Individual_set = HashSet( Individual_hash_key )

end

end (* functor Indis_functor *)

