(*
  File: constants.sml
  Created: 1998-09-02
  Modified: 2000-04-20
*)

structure Constants =
struct

(* Rprop parameters: *)

(*
val Eta_plus = 1.2
val Eta_minus = 0.5
val Initial_update_value = 0.1
val Max_update_value = 50.0
val Min_update_value = 1.0e~6


(* Bprop parameters: *)
val Learning_rate = 0.075
val Momentum = 0.9

val Number_of_nn_post_opt_epochs = 64
*)

  val Default_no_of_cases_distribution =
    [ ( 0, 1.0/3.0 ), ( 1, 1.0/3.0 ), ( 2, 1.0/3.0 ) ]
  val Total_max_REQ_storage = 10000
  val No_of_REQs_distribution = [ 0.40, 0.30, 0.18, 0.12 ]
  val MULTIR_distribution = [ 0.60, 0.40 ]

  val Free_exp_synt_share = 0.3
  (* The TGI and nested call restrictions are turned off for the first
     Free_exp_synt_share * N synted exps. *)

val Arity_weights = [ 
    ( 8, 0.02 ),  
    ( 7, 0.02 ),
    ( 6, 0.02 ),
    ( 5, 0.02 ),
    ( 4, 0.04 ),
    ( 3, 0.08 ),
    ( 0, 0.20 ),
    ( 2, 0.28 ),
    ( 1, 0.32 ) 
    ]

val Alpha = 2.0
val Initial_cost_limit = 100.0

val Eval_sample_card = 10000
(* Note that a too small value of this parameter gives quite high variance
   in the fraction of programs that actually are given more eval time.
*)

val Tail_recursion_opt = true

(* Constants replicated in execute.c: *)

val Heap_size = 64000000
(* Heap size in words including size used to store inputs. *)

val Machine_code_size = 16000000 (* No of bytes. *)

val Act_array_size = 4000000 (* No of words. *)

val Buffer_size = 4000000
end (* structure Constants *)
