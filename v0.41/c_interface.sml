(*
  File: c_interface.sml.
  Created : 1996-08-12.
  Modified: 1996-08-19.
*)


signature C_INTERFACE =
sig

val Is_smlnj : bool

val poke : int * int -> int
val peek : int -> int
val poke_word : int * Word32.word -> unit
val blastWrite : 'a -> Word8Vector.vector
val blastRead : Word8Vector.vector * 'a -> 'a
val exportML : string -> bool
val GCmessages : bool -> unit

val Return_value_addr : Word32.word
val Saved_esp_addr : Word32.word
val Call_count_addr : Word32.word
val Q_sym_code_addr : Word32.word
val Status_addr : Word32.word
val Heap_top_addr : Word32.word
val Input_start_addr : Word32.word

val Heap_addr : Word32.word
val Heap_addr_int : int
val Machine_code_addr : Word32.word
val Act_array_addr : Word32.word

val mk_heap_sub_call : string -> string

val set_max_time : Word32.word -> unit

val execute' : Word32.word -> Word32.word * Word32.word * int * int * int
(* Clears the call count.
  (Address of f) * (Input_number) -> 
   (Status code) * (Boxed or unboxed execution result) * 
   (Call count) * (Allocation count) * (Q sym code)
*)

val read_act_array : int * int -> int vector
(* (First index) * (Last index) -> (Act vector) *)

val clear_act_array : int * int -> unit
(* (First index) * (Last index) -> () *)

val set_heap_top : Word32.word -> unit
val set_input_start : Word32.word -> unit

(*
val verify_addr : Word32.word -> Word32.word
*)

  
(* Addresses related to floating point: *)

val Tmp_addr  : Word32.word 
val Add_addr : Word32.word 
val Sub_addr : Word32.word 
val Mul_addr : Word32.word 
val Div_addr : Word32.word 
val Equal_addr : Word32.word 
val Less_addr : Word32.word 
val Sigmoid_addr : Word32.word 

val write_double : int * real -> unit
val read_double : int -> real

val real_to_doubleword : real -> Word32.word * Word32.word
val doubleword_to_real : Word32.word * Word32.word -> real

(* Levenberg-Marquardt functions: *)
(*
val Rconsts_addr : Word32.word
val Outputs_addr : Word32.word
val set_ml_fcn : (unit->unit)->unit
val lm_called_from_ml : int *int * int -> unit
*)

end (* signature C_INTERFACE *)


structure C_interface : C_INTERFACE =
struct
open Lib List1 


val Is_smlnj = true

val poke = poke
val peek = peek

fun poke_word( Location : int, X : Word32.word ) : unit = (
(*
      p"\npoke_word: Location ="; 
      p( Word32.toString( Word32.fromInt Location ) );
      p"  X = "; p(Word32.toString X ); flush_out( !std_out );
*)
      poke( Location, 
        Word8.toInt( Word8.fromLargeWord X ) );
      poke( Location+1, 
        Word8.toInt( Word8.fromLargeWord(Word32.>>( X, 0w8))));
      poke( Location+2, 
        Word8.toInt( Word8.fromLargeWord(Word32.>>( X, 0w16 ))));
      poke( Location+3, 
        Word8.toInt( Word8.fromLargeWord(Word32.>>( X, 0w24 ) ) ) );
      ()
      )


val blastWrite = Unsafe.blastWrite

fun blastRead( V, X ) = Unsafe.blastRead V

val exportML = SMLofNJ.exportML
val GCmessages = SMLofNJ.Internals.GC.messages

structure CI = CCalls(structure CCInfo = GCCInfoX86Linux);
open CI


structure CU = CUtil(structure C = CI);
open CU

val Max_time_addr : Word32.word = 
  case c_fun_max_time_addr [] of Cint X => X

val Return_value_addr : Word32.word = 
  case c_fun_return_value_addr [] of Cint X => X


val Saved_esp_addr  : Word32.word = 
  case c_fun_saved_esp_addr [] of Cint X => X
val Call_count_addr  : Word32.word = 
  case c_fun_call_count_addr [] of Cint X => X
val Q_sym_code_addr  : Word32.word = 
  case c_fun_q_sym_code_addr [] of Cint X => X
val Status_addr  : Word32.word = 
  case c_fun_status_addr [] of Cint X => X
val Heap_top_addr  : Word32.word = 
  case c_fun_heap_top_addr [] of Cint X => X
val Input_start_addr  : Word32.word = 
  case c_fun_input_start_addr [] of Cint X => X

val Heap_addr : Word32.word = 
  case c_fun_heap_addr [] of Cint X => X
val Heap_addr_int = Word32.toInt Heap_addr

val Machine_code_addr  : Word32.word =
  case c_fun_machine_code_addr [] of Cint X => X

val Act_array_addr  : Word32.word =
  case c_fun_act_array_addr [] of Cint X => X


  
fun mk_heap_sub_call( Index_arg : string ) : string = 
"\n(case Heap_addr_int + 4 * (" ^ Index_arg ^ 
") of XXX => Word32.fromInt( C_interface.peek( XXX ) ) ) \n"


exception Read_act_array_exn
fun read_act_array( First : int, Last : int ) : int Vector.vector = (
(*
  if !Ast.Debug then (
    output( !std_out,"r" );
    flush_out( !std_out )
    )
  else
    ();
*)
  if Last >= Constants.Act_array_size - 20 then
    raise Read_act_array_exn
  else if Last < First then
     Vector.tabulate( 0, fn I => 0 )
   else
   let
     val N = Last - First + 1
   in
     Vector.tabulate( N,
       fn I => peek( 
         Word32.toInt( Act_array_addr ) + 4 * ( First + I ) ) )
   end
   )

exception Clear_act_array_exn
fun clear_act_array( First : int, Last : int ) : unit = (
(*
  if !Ast.Debug then (
    output( !std_out,"c" );
    flush_out( !std_out )
    )
  else
    ();
*)
  if First < 0 orelse Last >= Constants.Act_array_size-20 then
    raise Clear_act_array_exn
  else if Last < First then () else
  case
    c_fun_clear_act_array[ Cint(Word32.fromInt First),
      Cint(Word32.fromInt Last) ]
  of
    _ => ()
  )

fun set_heap_top( To : Word32.word ) : unit = 
  poke_word( Word32.toInt Heap_top_addr, To )

fun set_input_start( To : Word32.word ) : unit = 
  poke_word( Word32.toInt Input_start_addr, To )

fun set_max_time( To : Word32.word ) : unit = 
  poke_word( Word32.toInt Max_time_addr, To )

fun execute'( Entry_point : Word32.word )
    : Word32.word * Word32.word * int * int * int = (
(*
  if !Ast.Debug then (
    output( !std_out,"e" );
    flush_out( !std_out )
    )
  else
    ();
*)
  case c_fun_execute[ Cint Entry_point ] of
    Cptr( Cstruct [ Cint Status_code, Cint Result, Cint Call_count,
        Cint Allocation_count, Cint Q_sym_code ] ) =>
      ( Status_code, Result, 
        Word32.toInt Call_count, 
        Word32.toInt Allocation_count,
        Word32.toInt Q_sym_code )
  )


local

  open Word32

in

exception Verify_addr_exn

fun verify_addr( Addr : Word32.word ) : Word32.word =
if 
  Addr = Return_value_addr orelse
  Addr = Saved_esp_addr orelse
  Addr = Call_count_addr orelse
  Addr = Q_sym_code_addr orelse
  Addr = Status_addr orelse
  Heap_addr <= Addr andalso Addr < Heap_addr + 0w4 * 0w300000 orelse
  Addr = Heap_top_addr orelse
  Machine_code_addr <= Addr andalso 
  Addr < Machine_code_addr + 0w1000000 orelse
  Act_array_addr <= Addr andalso Addr < Act_array_addr + 0w4 * 0w100000
then
  Addr
else
  raise Verify_addr_exn

end (* local *)
  
(* Code related to floating point: *)

val Tmp_addr : Word32.word =
  case c_fun_tmp_addr [] of Cint X => X

val Add_addr : Word32.word =
  case c_fun_add_addr [] of Cint X => X

val Sub_addr : Word32.word =
  case c_fun_sub_addr [] of Cint X => X

val Mul_addr : Word32.word =
  case c_fun_mul_addr [] of Cint X => X

val Div_addr : Word32.word =
  case c_fun_div_addr [] of Cint X => X

val Equal_addr : Word32.word =
  case c_fun_equal_addr [] of Cint X => X

val Less_addr : Word32.word =
  case c_fun_less_addr [] of Cint X => X

val Sigmoid_addr : Word32.word =
  case c_fun_sigmoid_addr [] of Cint X => X

val write_double : int * real -> unit =
  Unsafe.CInterface.c_function "SMLNJ-Math" "write_double"

val read_double : int -> real =
  Unsafe.CInterface.c_function "SMLNJ-Math" "read_double"

val real_to_doubleword : real -> Word32.word * Word32.word =
  Unsafe.CInterface.c_function "SMLNJ-Math" "real_to_doubleword"

val doubleword_to_real : Word32.word * Word32.word -> real =
  Unsafe.CInterface.c_function "SMLNJ-Math" "doubleword_to_real"

(*
val Rconsts_addr  : Word32.word = 
  case c_fun_rconsts_addr [] of Cint X => X
val Outputs_addr  : Word32.word = 
  case c_fun_outputs_addr [] of Cint X => X

val set_ml_fcn = fn run =>
  case set_ml_fcn[ Cfunction( fn [] => ( run(); Cint 0w0 ) ) ] of _ => ()

val lm_called_from_ml = fn( M, N, Maxfev ) =>
  case lm_called_from_ml[ 
         Cint( Word32.fromInt M ),
         Cint( Word32.fromInt N ),
         Cint( Word32.fromInt Maxfev ) ]
  of _ => ()
*)
         



end (* structure C_interface *)
