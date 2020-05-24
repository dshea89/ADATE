(* cutil.sml
 *
 * COPYRIGHT (c) 1995 AT&T Bell Laboratories.
 *
 * functor producing structures with useful user C functions.
 *)

functor CUtil (structure C: C_CALLS) : C_UTIL =
struct
	open C

	val ptos' = registerAutoFreeCFn("ptos",[CaddrT],CstringT)
	fun ptos p = let val Cstring s = ptos' [Caddr p] in s end
        val ptoi' = registerAutoFreeCFn("ptoi",[CaddrT],CintT)
        fun ptoi p = let val Cint i = ptoi' [Caddr p] in i end
      
(*
  val test_inc' = registerAutoFreeCFn("test_inc",[CintT],CintT)
  fun test_inc x = let val Cint x = test_inc' [Cint x] in x end
*)

  val c_fun_max_time_addr = 
    registerAutoFreeCFn( "c_fun_max_time_addr", [], CintT )

  val c_fun_return_value_addr = 
    registerAutoFreeCFn( "c_fun_return_value_addr", [], CintT )

  val c_fun_saved_esp_addr = 
    registerAutoFreeCFn( "c_fun_saved_esp_addr", [], CintT )

  val c_fun_call_count_addr = 
    registerAutoFreeCFn( "c_fun_call_count_addr", [], CintT )

  val c_fun_q_sym_code_addr = 
    registerAutoFreeCFn( "c_fun_q_sym_code_addr", [], CintT )

  val c_fun_status_addr = 
    registerAutoFreeCFn( "c_fun_status_addr", [], CintT )

  val c_fun_machine_code_addr = 
    registerAutoFreeCFn( "c_fun_machine_code_addr", [], CintT )

  val c_fun_act_array_addr = 
    registerAutoFreeCFn( "c_fun_act_array_addr", [], CintT )

  val c_fun_heap_addr = 
    registerAutoFreeCFn( "c_fun_heap_addr", [], CintT )

  val c_fun_heap_top_addr = 
    registerAutoFreeCFn( "c_fun_heap_top_addr", [], CintT )

  val c_fun_input_start_addr = 
    registerAutoFreeCFn( "c_fun_input_start_addr", [], CintT )


  val c_fun_execute = 
    registerAutoFreeCFn( "c_fun_execute", 
      [ CintT ], 
      CptrT(CstructT [ CintT, CintT, CintT, CintT, CintT ]) )

  val c_fun_clear_act_array = 
    registerAutoFreeCFn( "c_fun_clear_act_array", 
      [ CintT,  CintT ], CvoidT )

(* Functions related to floating point: *)

  val c_fun_tmp_addr = 
    registerAutoFreeCFn( "c_fun_tmp_addr", [], CintT )

  val c_fun_add_addr = 
    registerAutoFreeCFn( "c_fun_add_addr", [], CintT )


  val c_fun_sub_addr = 
    registerAutoFreeCFn( "c_fun_sub_addr", [], CintT )

  val c_fun_mul_addr = 
    registerAutoFreeCFn( "c_fun_mul_addr", [], CintT )


  val c_fun_div_addr = 
    registerAutoFreeCFn( "c_fun_div_addr", [], CintT )


  val c_fun_equal_addr = 
    registerAutoFreeCFn( "c_fun_equal_addr", [], CintT )


  val c_fun_less_addr = 
    registerAutoFreeCFn( "c_fun_less_addr", [], CintT )

  val c_fun_sigmoid_addr = 
    registerAutoFreeCFn( "c_fun_sigmoid_addr", [], CintT )





  val mpi_init = 
    registerAutoFreeCFn( "mpi_init", 
      [ CintT, CaddrT], CvoidT )

  val mpi_comm_rank = 
    registerAutoFreeCFn( "mpi_comm_rank", [], CintT )

  val mpi_comm_size = 
    registerAutoFreeCFn( "mpi_comm_size", [], CintT )

  val mpi_any_source = 
    registerAutoFreeCFn( "mpi_any_source", [], CintT )

  val c_fun_buffer_addr = 
    registerAutoFreeCFn( "c_fun_buffer_addr", [], CintT )

  val mpi_send = 
    registerAutoFreeCFn( "mpi_send", 
      [ CintT, CintT, CintT ], CvoidT )


  val mpi_recv = 
    registerAutoFreeCFn( "mpi_recv", 
      [ CintT, CintT ], 
      CptrT(CstructT [ CintT, CintT, CintT, CintT ]) )


  val mpi_finalize = 
    registerAutoFreeCFn( "mpi_finalize", [], CvoidT )



(*
  val c_fun_rconsts_addr = 
    registerAutoFreeCFn( "c_fun_rconsts_addr", [], CintT )

  val c_fun_outputs_addr = 
    registerAutoFreeCFn( "c_fun_outputs_addr", [], CintT )

  val set_ml_fcn = 
    registerAutoFreeCFn( "set_ml_fcn", 
      [ CfunctionT( [], CintT) ],
      CvoidT )


  val lm_called_from_ml = 
    registerAutoFreeCFn( "lm_called_from_ml", 
      [ CintT, CintT, CintT ], 
      CvoidT )
*)

end (* functor CUtil *)
