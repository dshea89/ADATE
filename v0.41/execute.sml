(*
  File: execute.sml
  Created: 1996-08-07.
  Modified: 2000-01-14.

Modified 1999-12-01 to handle Validation_inputs. No activation checking
is done for validation inputs.

Modified 2000-01-14 to avoid overflow of activation counts.
*)

signature EXECUTE =
sig

val initialize : string -> unit
val reinitialize : string -> unit

structure Spec : SPEC

datatype execution_status = 
    ok_status of Spec.output_type
  | q_sym_status of Ast.symbol
  | call_count_overflow_status
  | heap_overflow_status

val set_max_time : int -> unit

val compile_f_dec : 
  ('1a,'1b)Ast.d-> unit Ast.Symbol_HashTable.hash_table * real
(* Returns ( Names of functons without global vars, Activation sum for 
   spec defs ). The second coord shouls be subtracted from the act sum returned
   by finish. *)


val execute : int -> execution_status * int * int
(* Argument: Input number, say No. Validation input used
   if No >= length Spec.Inputs. Second return value : Call count. 
   Third return value: Allocation count measured in no of words. *)

val finish : ('1a,'1b)Ast.d -> int Vector.vector Array.array * real
(* Updates the activation counts in f dec. Returns Problem_act_matrix and
   activation count sum . *)

val execute_time : unit -> real
val total_execute_time : unit -> real
val finish_time : unit -> real
val act_array_time : unit -> real
val vector_to_output_time : unit -> real
val execute_aux_time : unit -> real
val compile_etc_time : unit -> real
val bm_execute : Ast.dec * int -> real
val bm_compile : Ast.dec * int -> real

end




functor Execute_functor( structure Spec : SPEC ) : EXECUTE =
struct
open Lib List1 Ast Ast_lib Produce_super_combs Compile 
  Assemble_link_and_load Spec

structure Spec = Spec
exception Inputs_is_null_exn
val () = if null Spec.Inputs then raise Inputs_is_null_exn else ()

datatype execution_status = 
    ok_status of Spec.output_type
  | q_sym_status of Ast.symbol
  | call_count_overflow_status
  | heap_overflow_status

val Current_max_time = ref 100000

fun set_max_time( N : int ) : unit = (
  C_interface.set_max_time( Word32.fromInt N );
  Current_max_time := N
  )

structure H = Symbol_HashTable

fun input_to_vector( Start_addr : Word32.word, X : input_type )
    : Word32.word vector = (
  Make_spec.Dynarr_top := 0;
  input_type_to_dynarr( Start_addr, X );
  Vector.tabulate( !Make_spec.Dynarr_top,
    fn I => Word32_dyn.sub( Make_spec.Dynarr, I ) )
  )


val Problem_act_matrix : int Vector.vector Array.array = 
  Array.array( length Spec.Inputs, Vector.fromList [] )
(* Employed in evaluate.sml to compute the error locality measure. *)

val Initialized = ref false
val Next_free_act_index = ref 1
val Spec_fun_decs : dec list ref = ref []
val Spec_supers : dec list ref = ref []

val Assembly_code : instruction Array.array = 
  Array.array( Constants.Machine_code_size div 16, (nop,none,none) )
val Assembly_code_top = ref 0

val Q_sym_map = Symbol_dyn.array( 2, DUMMY_SYMBOL )
val Q_sym_map_top = ref 0

val Machine_code_for_f_addr = ref( Word32.fromInt 0 )

val Last_act_index = ref 0

val Max_N_execute_calls  = max2( op<, 1, 
  (Max_int div 3) div max( op<, Spec.Max_time_distribution ) )

exception Fun_entry_table_exn
val Fun_entry_table : int H.hash_table = 
  H.mkTable( 10, Fun_entry_table_exn )
(* Maps a function to its start index in Assembly_code. To be initialized with
   functions defined in the specification.
*)

val Total_no_of_inputs = length Inputs + length Validation_inputs

val Input_starts = Array.array( Total_no_of_inputs+1, 0w0 : Word32.word )
val () =
  Array.update( Input_starts, 0, C_interface.Heap_addr )

fun store_inputs() : unit =
  loop( fn(I,Inp) =>
    let
      val V = input_to_vector( Array.sub( Input_starts, I ), Inp )
      val N = Vector.length V
    in
      Array.update( Input_starts, I+1,
        Word32.+( Array.sub( Input_starts, I ), Word32.fromInt( 4*N ) ) );

      for( 0, N-1, fn K =>
        C_interface.poke_word( 
          Word32.toInt( Array.sub( Input_starts, I ) ) + 4*K,
          Vector.sub( V, K ) ) )
    end,
    combine( fromto( 0, Total_no_of_inputs - 1 ), Inputs@Validation_inputs ) )


fun un( Instr : instruction ) : unit = (
  Array.update( Assembly_code, !Assembly_code_top, Instr );
  inc Assembly_code_top
  )

fun add_handler_code() = (
  Q_sym_map_top := 0;
  Assembly_code_top := 0;
  H.insert Fun_entry_table ( Q_sym_handler_sym, !Assembly_code_top );
  un( mov, register esp, direct C_interface.Saved_esp_addr );
  un( mov, direct C_interface.Call_count_addr, register edx );
  un( mov, direct C_interface.Heap_top_addr, register edi );
  un( mov, direct C_interface.Status_addr, immediate 0w1 );
  un( popa, none, none );
  un( ret, none, none );

  H.insert Fun_entry_table 
    ( Call_count_overflow_handler_sym, !Assembly_code_top );
  un( mov, register esp, direct C_interface.Saved_esp_addr );
  un( mov, direct C_interface.Call_count_addr, register edx );
  un( mov, direct C_interface.Heap_top_addr, register edi );
  un( mov, direct C_interface.Status_addr, immediate 0w2 );
  un( popa, none, none );
  un( ret, none, none );

  H.insert Fun_entry_table 
    ( Heap_overflow_handler_sym, !Assembly_code_top );
  un( mov, register esp, direct C_interface.Saved_esp_addr );
  un( mov, direct C_interface.Call_count_addr, register edx );
  un( mov, direct C_interface.Heap_top_addr, register edi );
  un( mov, direct C_interface.Status_addr, immediate 0w3 );
  un( popa, none, none );
  un( ret, none, none );
  un( align, immediate 0w16, none )
  )

exception Add_init_code
fun add_init_code() = 
  let
    val Arity =
      case Predefined.input_type() of
        ty_con_exp( Ty_con, Args as _::_::_ ) =>
          if Ty_con <> TUPLE_TY_CON then
            raise Add_init_code
          else
            length Args
       | ty_con_exp( _, nil ) => 1
  in
  un( pusha, none, none );
  un( mov, direct C_interface.Saved_esp_addr, register esp );
  un( mov, register edx, direct C_interface.Call_count_addr );
  un( mov, register edi, direct C_interface.Heap_top_addr );

  un( mov, register eax, direct C_interface.Input_start_addr );

  loop( fn I =>
    un( 
      push, 
      indexed( eax, Word32.fromInt( 4 * (Arity-I) ) ), 
      none ),
    fromto(1,Arity) );
  un( call, label( string_to_symbol(func_sym,"f") ), none );

(*
  un( push, register ebp, none );
  un( mov, register ebp, register esp );
  un( mov, register ebx, indexed(ebp,0w4) );
  un( jz, label Heap_overflow_handler_sym, none );
  un( pop, register ebp, none );
*)

  un( add, register esp, immediate(Word32.fromInt(4*Arity)) );
  un( mov, direct C_interface.Return_value_addr, register ebx );
  un( mov, direct C_interface.Call_count_addr, register edx );
  un( mov, direct C_interface.Heap_top_addr, register edi );
  un( mov, direct C_interface.Status_addr, immediate 0w0 );
  un( popa, none, none );
  un( ret, none, none );
  un( align, immediate 0w16, none )
  end 

fun next_q_sym( Q_sym : symbol ) : int =
  let
    val Code = !Q_sym_map_top
  in
    inc Q_sym_map_top;
    Symbol_dyn.update( Q_sym_map, Code, Q_sym );
    Code
  end


val Execute_timer = mk_timer "Execute_timer"
fun execute_time() = check_timer Execute_timer

val Compile_etc_timer = mk_timer "Compile_etc_timer"
fun compile_etc_time() = check_timer Compile_etc_timer

fun inline() =
let
  val C = compile_etc_time()
  val E = execute_time()
in
  C * 1.5 + E / 1.2 + 1.0 < C + E
end

val Top_of_heap_after_spec_funs = ref( 0w0 : Word32.word )

exception Recompile_spec_funs
fun recompile_spec_funs() = (
  start_timer Compile_etc_timer;
  if !Initialized then () else raise Recompile_spec_funs;
  add_handler_code();
  case compile_supers(
    NONE,
    Fun_entry_table,
    next_q_sym,
    !Spec_supers,
    !Assembly_code_top,
    Assembly_code,
    inline(),
    Array.sub( Input_starts, Total_no_of_inputs )
    ) of X => 
     ( Assembly_code_top := #1 X; Top_of_heap_after_spec_funs := #2 X );
  Machine_code_for_f_addr := assemble_link_and_load(
    Assembly_code, 0, !Assembly_code_top - 1, Fun_entry_table,
      C_interface.Machine_code_addr );
  stop_timer Compile_etc_timer
  )

fun compile_spec_funs() : unit = (
  Spec_fun_decs := Predefined.fun_decs();
  Next_free_act_index := add_act_indices( !Spec_fun_decs, 1 );
  Spec_supers := #1( make_super_combs( !Spec_fun_decs ) );
  recompile_spec_funs()
  )

exception Execute_initialize
fun initialize( Spec_file : string ) : unit = (
  if !Initialized then raise Execute_initialize else ();
  Compile.initialize( Spec_file, Spec.Abstract_types );
  store_inputs();
  Initialized := true;
  compile_spec_funs();
  C_interface.clear_act_array( 0, !Next_free_act_index - 1 )
  )

fun reinitialize( Spec_file : string ) : unit = (
  store_inputs();
  recompile_spec_funs();
  C_interface.clear_act_array( 0, !Next_free_act_index - 1 )
  )


fun sum_vector( V : int Vector.vector ) : real = 
  let
    val S = ref 0.0
  in
    loop( fn I => ( S := real( Vector.sub( V, I ) ) + (!S) ), 
      fromto( 0, Vector.length V - 1 ) );
    !S
  end
    

fun sum_real_vector( V : real Vector.vector ) : real = 
  let
    val S = ref 0.0
  in
    loop( fn I => ( S := Vector.sub( V, I ) + (!S) ), 
      fromto( 0, Vector.length V - 1 ) );
    !S
  end
    

val Top_of_heap_after_f = ref( 0w0 : Word32.word )

fun compile_f_dec( D : ('1a,'1b)d ) : unit H.hash_table * real=
  let
    val Act_spec =  
      C_interface.read_act_array( 0, !Next_free_act_index - 1 )
    val Next_free = add_act_indices( [D], !Next_free_act_index )
    val _ =  ( 
      Last_act_index := Next_free - 1;
      C_interface.clear_act_array( !Next_free_act_index, !Last_act_index )
      )
    val ( Supers, No_globals ) = make_super_combs( [ D ] )
    val Saved_Q_sym_map_top = !Q_sym_map_top
    val Asm_start = !Assembly_code_top
    val _ = add_init_code()
    val ( Asm_top, X ) = compile_supers(
      SOME( !Spec_supers ),
      Fun_entry_table,
      next_q_sym,
      Supers,
      !Assembly_code_top,
      Assembly_code,
      inline(),
      !Top_of_heap_after_spec_funs
      )
  in
    Top_of_heap_after_f := X;
    assemble_link_and_load( Assembly_code, Asm_start, Asm_top - 1,
      Fun_entry_table, !Machine_code_for_f_addr );
    Q_sym_map_top := Saved_Q_sym_map_top;
    Assembly_code_top := Asm_start;
    loop( fn{ func, ... } => H.remove Fun_entry_table func, Supers );
    ( No_globals, sum_vector Act_spec )
  end
  handle Ex => (
    output( !std_err, "compile_f_dec :  " );
    Print.print_dec' D;
    flush_out( !std_err );
    re_raise( Ex, "compile_f_dec" )
    )

val compile_f_dec = fn X => 
let
  val () = start_timer Compile_etc_timer
  val Y = compile_f_dec X
in
  stop_timer Compile_etc_timer;
  Y
end
  

local

fun vector_max( V : real vector ) : real =
  Vector.foldl (fn(X,Y) => max2(op<,X,Y)) (~1.0E99) V

exception Scale_act_vector_exn
fun scale_act_vector( V : real vector, Scale : real ) : real vector =
  if Scale < 0.9999999 then raise Scale_act_vector_exn else
  Vector.map (fn N => N / Scale) V

fun increase_act_indices( {exp, ...} : ('1a,'1b)d, Act_vector : real vector ) =
  act_info_loop( 
    fn{ act_index, act_count, activated, ... } => 
      case floor( Vector.sub( Act_vector, !act_index ) ) of X => (
      act_count := !act_count + X;
      activated := X > 0
      ),
    exp )

fun max_act_count( { exp, ... } : ('1a,'1b)d ) =
  let
    val M = ref 0
  in
    act_info_loop( fn{ act_count, ... }  =>
        if !act_count > !M then M := !act_count else (),
      exp );
    !M
  end
     
exception Scale_act_counts
fun scale_act_counts( D : ('1a,'1b)d, Scale : int) =
  if Scale < 1 then raise Scale_act_counts else
    act_info_loop( fn{ act_count, ... } =>
        act_count := !act_count div Scale,
      #exp D );

in (* local *)

fun update_act_indices( D : ('1a,'1b)d, Act_vector : real vector ) = 
let
  val M1 = real( max_act_count D )
  val M2 = vector_max Act_vector
  val M = M1+M2
  val Scale = M / real Max_int
  val Scale = ceil Scale
  val Act_vector =
    if Scale < 1 then Act_vector else (
      scale_act_counts( D, Scale );
      scale_act_vector( Act_vector, real Scale ) )
in
  increase_act_indices( D, Act_vector )
end
handle Ex => (
  output(!std_err, "\nupdate_act_indices :\n" );
  Print.print_dec_act_info D;
  flush_out( !std_err );
  re_raise( Ex, "update_act_indices" )
  )

end (* local *)

val Execute_aux_timer = mk_timer "Execute_aux_timer"
fun execute_aux_time() = check_timer Execute_aux_timer


local

val Recompile_timer = mk_timer "Recompile_timer"
val () = start_timer Recompile_timer

in

fun recompile_check() : bool =
  case check_timer Recompile_timer of T =>
  if T < 1000.0 then
    false
  else (
    set_timer( Recompile_timer, 0.0 );
    true )

end
    




local

val N_execute_calls = ref 0

val Finish_timer = mk_timer "Finish_timer"

in

fun finish_time() = check_timer Finish_timer

fun finish( D : ('1a,'1b)d ) =
  if !Last_act_index = ~1 then ( Problem_act_matrix, 0.0 ) else
  let
    val Act_spec =  
      C_interface.read_act_array( 0, !Next_free_act_index - 1 )
    val V = Vector.tabulate( !Last_act_index+1, fn Rhs_no =>
      if Rhs_no < !Next_free_act_index then
        real( Vector.sub( Act_spec, Rhs_no ) )
      else
        let
          val Rhs_no = Rhs_no - !Next_free_act_index
          val Sum = ref 0.0
        in
          for( 0, Array.length Problem_act_matrix - 1, fn Problem_no =>
            Sum := !Sum + real(
              Vector.sub( Array.sub( Problem_act_matrix, Problem_no ),
                Rhs_no ) ) );
          !Sum
        end )

  in
      start_timer Execute_aux_timer;
    update_act_indices( D, V );
      stop_timer Execute_aux_timer;
    if !N_execute_calls < Max_N_execute_calls then
      ()
    else (
      N_execute_calls := 0;
      loop( fn D => update_act_indices( D, V ), !Spec_fun_decs );
      C_interface.clear_act_array( 0, !Next_free_act_index - 1 );
      if recompile_check() then recompile_spec_funs() else ()
      );
    ( Problem_act_matrix, sum_real_vector V ) 
  end
handle Ex => (
  output(!std_err, "\nfinish :\n" );
  flush_out( !std_err );
  re_raise( Ex, "finish" )
  )

val finish = fn X => 
let
  val () = start_timer Finish_timer
  val Y = finish X
in
  stop_timer Finish_timer;
  Y
end

fun word32_is_int( X : Word32.word ) : bool =
  ( case Word32.toIntX X of X => ~Max_int < X andalso X < Max_int )
  handle _ => false

(*
val Crash_timer = mk_timer "Crash_timer"
val _ = start_timer Crash_timer
*)
val Act_array_timer = mk_timer "Act_array_timer"
fun act_array_time() = check_timer Act_array_timer


val Vector_to_output_timer = mk_timer "Vector_to_output_timer"
fun vector_to_output_time() = check_timer Vector_to_output_timer

(*
val vector_to_output_type = fn X =>
let
  val () =  start_timer Vector_to_output_timer
  val Y = vector_to_output_type X
  val () =  stop_timer Vector_to_output_timer
in
  Y
end
*)
val Inputs_length = length Inputs

fun execute( Problem_no : int ) : execution_status * int * int = 
  let 
    val () = C_interface.set_heap_top( !Top_of_heap_after_f )
    val Validation = Problem_no >= Inputs_length
    val _ = if Validation then () else inc N_execute_calls

    val ( Status, Result, Call_count, Allocation_count, Q_sym_code ) = 
(*
      if check_timer Crash_timer < 120.0 then
*)
        (
        C_interface.set_input_start( Array.sub( Input_starts, Problem_no ) );
        start_timer Execute_timer;
        case C_interface.execute'( !Machine_code_for_f_addr ) of Z => (
        stop_timer Execute_timer;
          Z ) )
(*
      else (* Cause a crash! *)
        C_interface.execute'( 0w8000000, Problem_no )
*)
  
  in
(*
    output( !std_out, "\nStatus = " ^ Word32.toString Status ^
      "\nResult = " ^ Word32.toString Result ^
      "\nCall_count = " ^ Int.toString Call_count ^
      "\nQ_sym_code = " ^ Int.toString Q_sym_code 
      );
    flush_out( !std_out );
*)

  if Validation then () else (
    (* start_timer Act_array_timer; *)
    case C_interface.read_act_array( !Next_free_act_index, !Last_act_index ) 
    of Xs => 
      Array.update( Problem_act_matrix, Problem_no, Xs );
    C_interface.clear_act_array( !Next_free_act_index, !Last_act_index )
    (* stop_timer Act_array_timer *)
  );
let
  val Y =
  case Word32.toInt Status of
    0 =>   
      if Spec.Output_type_is_unboxed andalso not( word32_is_int Result ) then
        ( heap_overflow_status, Call_count, Allocation_count ) (* Is actually int overflow. *)
      else  
      let
        val Result =  
         if Spec.Output_type_is_unboxed then
           Word32.toIntX Result
         else
           Word32.toInt(Word32.-( Result, C_interface.Heap_addr )) div 4

      in
        ( ok_status( vector_to_output_type(
                        C_interface.Heap_addr, 
                        Result ))
           handle Make_spec.Heap_overflow_exn => heap_overflow_status
                | Ex => (
                    output(!std_err, 
                      "\nvector_to_output_type in execute.sml:\n" );
                    flush_out( !std_err );
                    re_raise( Ex, "execute" )
                    ),
           Call_count, Allocation_count )
      end
  | 1 => ( q_sym_status( 
             if Q_sym_code < !Q_sym_map_top then
               PREDEFINED_NOT_ACTIVATED_SYMBOL
             else
               Symbol_dyn.sub( Q_sym_map, Q_sym_code )),
           Call_count, Allocation_count )
  | 2 => ( call_count_overflow_status, Call_count, Allocation_count )
  | 3 => ( heap_overflow_status, Call_count, Allocation_count )
in
  Y
end
  end
handle Ex => (
  output(!std_err, "\nexecute :\n" );
  flush_out( !std_err );
  re_raise( Ex, "execute" )
  )

(* The following is motivated by avoiding adaption with the sole purpose
   of causing a quick heap overflow in order to cut down on time complexity. 
*)
val Total_execute_timer = mk_timer "Total_execute_timer"
fun total_execute_time() = check_timer Total_execute_timer

val execute = fn Problem_no =>
let
  val () = start_timer Total_execute_timer
  val Y =
    case execute Problem_no of
      X as ( ok_status _, _, _ ) => X
    | X as ( q_sym_status _, _, _ ) => X
    | X as ( call_count_overflow_status, _, _ ) => X
    | ( heap_overflow_status, _, Allocation_count ) => 
        ( heap_overflow_status, !Current_max_time, 0 ) 
in
  stop_timer Total_execute_timer;
  Y
end
    
end (* local *)

exception Bm_execute_exn
fun bm_execute( D : dec, N : int ) : real = 
  if N > Max_N_execute_calls then raise Bm_execute_exn else (
  compile_f_dec D;
  let
    val T = mk_timer "bm_execute"
  in
    start_timer T;
    loop( fn I =>
      loop( fn J => execute J, fromto( 0, length Spec.Inputs - 1 ) ),
      fromto( 1, N ) );
    case check_timer T of N => ( delete_timer T; N )
  end
  )
    
fun bm_compile( D : dec, N : int ) : real =
  let
    val T = mk_timer "bm_compile"
  in
    start_timer T;
    loop( fn I => compile_f_dec D, fromto( 1, N ) );
    case check_timer T of N => ( delete_timer T; N )
  end

    


end (* functor Execute_functor *)

