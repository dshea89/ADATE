(* cutil.sig.sml
 *
 * COPYRIGHT (c) 1995 AT&T Bell Laboratories.
 *
 * Signature for structure containing some useful user C functions.
 *)
signature C_UTIL = 
sig
	type caddr
        type cdata

	val ptos : caddr -> string
	val ptoi : caddr -> Word32.word
       
       (* val test_inc : Word32.word -> Word32.word *)
  val c_fun_max_time_addr : cdata list -> cdata

  val c_fun_return_value_addr : cdata list -> cdata
  val c_fun_saved_esp_addr : cdata list -> cdata
  val c_fun_call_count_addr : cdata list -> cdata
  val c_fun_q_sym_code_addr : cdata list -> cdata
  val c_fun_status_addr : cdata list -> cdata
  val c_fun_machine_code_addr : cdata list -> cdata
  val c_fun_act_array_addr : cdata list -> cdata
  val c_fun_heap_addr : cdata list -> cdata
  val c_fun_heap_top_addr : cdata list -> cdata
  val c_fun_input_start_addr : cdata list -> cdata

  val c_fun_execute : cdata list -> cdata
  val c_fun_clear_act_array : cdata list -> cdata

  val c_fun_tmp_addr : cdata list -> cdata
  val c_fun_add_addr : cdata list -> cdata
  val c_fun_sub_addr : cdata list -> cdata
  val c_fun_mul_addr : cdata list -> cdata
  val c_fun_div_addr : cdata list -> cdata

  val c_fun_equal_addr : cdata list -> cdata
  val c_fun_less_addr : cdata list -> cdata
  val c_fun_sigmoid_addr : cdata list -> cdata

  val mpi_init : cdata list -> cdata
  val mpi_comm_rank : cdata list -> cdata
  val mpi_comm_size : cdata list -> cdata
  val mpi_any_source : cdata list -> cdata
  val c_fun_buffer_addr : cdata list -> cdata
  val mpi_send : cdata list -> cdata
  val mpi_recv : cdata list -> cdata
  val mpi_finalize : cdata list -> cdata

(*
  val c_fun_rconsts_addr : cdata list -> cdata
  val c_fun_outputs_addr : cdata list -> cdata
  val set_ml_fcn : cdata list -> cdata
  val lm_called_from_ml : cdata list -> cdata
*)
  
end (* signature C_UTIL *)
