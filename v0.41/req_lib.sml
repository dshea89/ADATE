(* File: req_lib.sml.
   Created 1998-04-20.
   Modified 1999-08-07.
*)

structure REQ_lib :
sig

val Offset : int
val estimate_K : int * int * real * int -> real option
val second_run_needed : int * int * real -> bool

val K_bis : real * int -> real

val choices_in_reqs_and_mults : ('a * int)list * int *
      ( { REQ_record : 'a, order_no : int } -> bool ) -> unit

type req_match_error_data

val initial_req_match_error_data : unit -> req_match_error_data
(* To be used for the initial indi and for each produced child. *)

val dummy_req_match_error_data : unit -> req_match_error_data
val req_match_error_data_clone : req_match_error_data -> req_match_error_data
val next_req_match_error_data : req_match_error_data -> req_match_error_data
(* To be used when finishing compound trf synt for an individual to prepare
   for the next compound trf synt for the same individual. *)

val match_error_update_and_estimate : 
      req_match_error_data * bool * bool * real * real -> real

val update_req_cost_limit_sum : 
      req_match_error_data * bool * bool * real -> unit

val print_req_match_error_data : req_match_error_data -> unit
val req_match_error_data_pack : req_match_error_data -> string
val req_match_error_data_unpack : string -> req_match_error_data
end =
struct


open Lib List1 Ast_lib5

val Offset = 5

fun iw'( REQ_card : int, REQ_PQ_card : int, Taken : bool,
      K : real, Cost_limit : real, Cost : real, No_of_REQs : int, 
      Max_so_far : int, Iw :  real ref ) : unit = 
  if K * Cost * real_pow( real Max_so_far + 1.0 + real Offset, 
                          real No_of_REQs ) > 
     Cost_limit 
  then
    ()
  else if No_of_REQs = 0 then
    Iw := !Iw + 1.0 / ( K * Cost )
  else
  let
    val Lower = Max_so_far + 1
(*
    val _ = p( "K = " ^ Real.toString K ^ "\n" )
    val _ = p( "Cost = " ^ Real.toString Cost ^ "\n" )
    val _ = p( "Lower = " ^ Int.toString Lower ^ "\n" )
    val _ = p( "No_of_REQs = " ^ Int.toString No_of_REQs ^ "\n" )
    val _ = p( "Cost_limit = " ^ Real.toString Cost_limit ^ "\n" )
*)
    val Upper = 
      floor(
      min2( op<,
        Cost_limit / ( Cost * K * 
          real_pow( real Lower + 1.0 + real Offset, 
                    real( No_of_REQs - 1 ) ) ) - 
        real Offset,
        real( if Taken then REQ_PQ_card else REQ_card )
        ) )
  in
    for( Lower, Upper,
      fn X =>
        iw'( REQ_card, REQ_PQ_card, if X > REQ_PQ_card then true else Taken,
          K, Cost_limit, Cost * ( real X + real Offset ), 
          No_of_REQs - 1, X, Iw ) )
  end

fun iw( REQ_card, REQ_PQ_card, K, Cost_limit, No_of_REQs ) : real = 
let
  val Iw = ref 0.0
in
  iw'( REQ_card, REQ_PQ_card, false, K, Cost_limit, 1.0, No_of_REQs, 0, Iw );
  !Iw
end


local

fun fact 0 = 1
  | fact N = N * fact( N - 1 )

open Math

in


fun K_bis( Cost_limit : real, No_of_REQs : int ) : real =
let
(*
  val () = ( p"\nstarting K_bis "; print_real Cost_limit; 
             flush_out( !std_out ) )
*)
  val N = real No_of_REQs
  val N_fact = real( fact No_of_REQs )
  val N_fact2 = N_fact * N_fact
  fun next Z =
    let
      val U = ln( Cost_limit / ( real_pow( real Offset + 1.0, N ) * Z ) )
    in
      Z - ( Z - real_pow( U, N ) / N_fact2 ) /
          ( 1.0 + N * real_pow( U, N - 1.0 ) / ( Z * N_fact2 ) )
    end
  fun search Z =
    let 
      val Z' = next Z
    in
      if Real.abs( Z' / Z - 1.0 ) < 1.0E~3 then
        Z'
      else
        search Z'
    end

  val Z0 = min2( op<, Cost_limit / ( 1.1 * real_pow( real Offset + 1.0, N ) ), 
                      1.0E4 )
  val Y = search Z0 
in
(* p"\nending K_bis"; flush_out( !std_out ); *)
  Y
end (* fun K_bis *)

end (* local *)



local

exception Too_many_f_calls

in

exception Estimate_K_not_tested_exn
exception Estimate_K_exn1
exception Estimate_K_exn2
fun estimate_K( REQ_card, REQ_PQ_card, Cost_limit, No_of_REQs ) : real option =
(* REQ_card is the total number of REQs tried in the first position i.e., the
   sum of the REQ_PQ cardinality and the on-the-fly cardinality.
   REQ_PQ_card is actually the length of the req_pq prefix of the merged
   map produced by the function merge in the functor Map.
*)
  if No_of_REQs > 4 then raise Estimate_K_not_tested_exn else
  if REQ_card < REQ_PQ_card then raise Estimate_K_exn1 else
  if REQ_card = 0 orelse REQ_PQ_card = 0 orelse Cost_limit < 1.0 then NONE else
  let
(*
    val _ = p "\nestimate_K:\n"
    val _ = p( "  REQ_card = " ^ Int.toString REQ_card )
    val _ = p( "  REQ_PQ_card = " ^ Int.toString REQ_PQ_card )
    val _ = p( "  Cost_limit = " ^ Real.toString Cost_limit )
    val _ = p( "  No_of_REQs = " ^ Int.toString No_of_REQs )
    val _ = nl()
*)
    val N = ref 0
    val Start = K_bis( Cost_limit, No_of_REQs )
    fun f K = 
      let 
        val Iw = iw( REQ_card, REQ_PQ_card, K, Cost_limit, No_of_REQs ) 
      in
        if real_rep_eq( Iw, 0.0 ) then inc N else ();
        if !N > 1000 then raise Too_many_f_calls else ();
        Iw - 1.0
      end

    fun stop1 K =
      K * ( real REQ_card + real Offset ) *
        real_pow( real REQ_PQ_card + real Offset, 
                  real( No_of_REQs - 1 ) ) < 0.1
  

    fun stop( K1 : real, K2 ) : bool =
      if K1 < 1.0E~99 orelse K2 < 1.0E~99 then
        raise Estimate_K_exn2
      else
        Real.abs( K1 / K2 -1.0 ) < 1.0E~7
  in
    case
      Eq_solve_lib.eq_solve_is_start'( stop1, stop, false, f, 0.05, Start )
    of
      NONE =>
        Eq_solve_lib.eq_solve_is_start'( stop1, stop, false, f, 0.20, Start )
    | X => X
  end
  handle Too_many_f_calls => NONE
  
end (* local *)

exception Second_run_needed_exn
fun second_run_needed( REQ_card, REQ_PQ_card, Greatest_cost_limit : real ) 
    : bool =
  if Greatest_cost_limit < 1.0 orelse REQ_PQ_card < 0 orelse
     REQ_card < REQ_PQ_card
  then
    raise Second_run_needed_exn
  else
  REQ_card > REQ_PQ_card andalso
  let
    val SOME K = estimate_K( REQ_card, REQ_PQ_card, Greatest_cost_limit, 1 )
    val Max_order_no = floor( Greatest_cost_limit / K - 3.0 )
  in
    Max_order_no > REQ_PQ_card
  end


exception Choices_in_reqs_and_mults_exn1
exception Choices_in_reqs_and_mults_exn2
fun choices_in_reqs_and_mults(
      REQs_and_mults : ( 'a * int ) list,
      Last_chosen_order_no : int,
      emit : { REQ_record : 'a, order_no : int } -> bool
      ) : unit =
(* Is employed with 'a = REQ_record. *)
let
  val N = int_sum( map( #2, REQs_and_mults ) )
  val Last_chosen_order_no =
    if Last_chosen_order_no = ~ Max_int then
      0
    else if Last_chosen_order_no < 0 orelse Last_chosen_order_no > N  then
      raise Choices_in_reqs_and_mults_exn1
    else
      Last_chosen_order_no

  val Continue = ref true

  fun all( _, [] ) = ()
    | all( Order_no, ( Record, Mult ) :: Rms ) =
    if Mult < 0 then
      raise Choices_in_reqs_and_mults_exn2
    else if Mult = 0 then
      all( Order_no, Rms )
    else (
      ( if Order_no > Last_chosen_order_no then
          Continue := ( !Continue andalso 
                       emit{ REQ_record = Record, order_no = Order_no } )
        else
         () );
      (
      if !Continue then
        all( Order_no + 1, ( Record, Mult - 1 ) :: Rms )
      else
        () )
      )
in
  all( 1, REQs_and_mults )
end
handle Ex => (
  p"\n\nchoices_in_reqs_and_mults:\n";
  re_raise( Ex, "choices_in_reqs_and_mults" )
  )
   

type req_match_error_data = {
  last_req_cost_limit_sum : real,
  last_match_error_cost_limit_sum : real,
  current_req_cost_limit_sum :  real ref,
  current_match_error_cost_limit_sum : real ref 
  }

fun req_match_error_data_pack( { last_req_cost_limit_sum,
  last_match_error_cost_limit_sum,
  current_req_cost_limit_sum,
  current_match_error_cost_limit_sum  } : req_match_error_data 
  ) : string =
  pack[
    real_pack last_req_cost_limit_sum,
    real_pack last_match_error_cost_limit_sum,
    real_pack( !current_req_cost_limit_sum ),
    real_pack( !current_match_error_cost_limit_sum )
    ]
    



fun req_match_error_data_unpack( S : string ) : req_match_error_data =
  case unpack S of [ S1, S2, S3, S4 ] => { 
    last_req_cost_limit_sum = real_unpack S1,
    last_match_error_cost_limit_sum = real_unpack S2,
    current_req_cost_limit_sum = ref( real_unpack S3 ),
    current_match_error_cost_limit_sum = ref( real_unpack S4 ) 
    }


fun initial_req_match_error_data() = {
  last_req_cost_limit_sum = 0.0,
  last_match_error_cost_limit_sum = 0.0,
  current_req_cost_limit_sum = ref 0.0,
  current_match_error_cost_limit_sum = ref 0.0
  }


fun dummy_req_match_error_data() = {
  last_req_cost_limit_sum = 1.0E99,
  last_match_error_cost_limit_sum = 1.0E99,
  current_req_cost_limit_sum = ref 0.0,
  current_match_error_cost_limit_sum = ref 0.0
  }


fun req_match_error_data_clone( 
      { last_req_cost_limit_sum : real,
        last_match_error_cost_limit_sum : real,
        current_req_cost_limit_sum,
        current_match_error_cost_limit_sum 
        } : req_match_error_data ) = {
  last_req_cost_limit_sum = last_req_cost_limit_sum,
  last_match_error_cost_limit_sum = last_match_error_cost_limit_sum,
  current_req_cost_limit_sum = ref( !current_req_cost_limit_sum ),
  current_match_error_cost_limit_sum = 
    ref( !current_match_error_cost_limit_sum ) }

fun next_req_match_error_data( 
      { last_req_cost_limit_sum,
        last_match_error_cost_limit_sum,
        current_req_cost_limit_sum,
        current_match_error_cost_limit_sum 
        } : req_match_error_data ) = {
  last_req_cost_limit_sum = !current_req_cost_limit_sum,
  last_match_error_cost_limit_sum = !current_match_error_cost_limit_sum,
  current_req_cost_limit_sum = ref 0.0,
  current_match_error_cost_limit_sum = ref 0.0 }

exception Match_error_update_and_estimate_exn
exception Match_error_update_and_estimate_exn2
fun match_error_update_and_estimate( 
      { last_req_cost_limit_sum,
        last_match_error_cost_limit_sum,
        current_req_cost_limit_sum,
        current_match_error_cost_limit_sum 
        } : req_match_error_data,
      First_call : bool,
      First_run : bool,
      REQ_cost_limit : real,
      Cost_limit : real
      ) : real =
  if last_req_cost_limit_sum > 1.0E98 then 
    raise Match_error_update_and_estimate_exn2
  else
let
  val Estimated_match_error_cost_limit_sum =
    if last_match_error_cost_limit_sum < 30.0 then
      1.0E99
    else if last_req_cost_limit_sum < 1.0 then
      raise Match_error_update_and_estimate_exn
    else 
      REQ_cost_limit / last_req_cost_limit_sum * last_match_error_cost_limit_sum
in
  if First_call andalso First_run then 
    current_match_error_cost_limit_sum  := 
      !current_match_error_cost_limit_sum + Cost_limit
  else
    ();

  if not First_call then Cost_limit else
    max2( op<, 0.0, max2( op<, Cost_limit,
      if last_match_error_cost_limit_sum < 30.0 orelse
           !current_match_error_cost_limit_sum > 
           0.6 * !current_req_cost_limit_sum (* Emergency brake. *)
        then
          0.0
        else
          Cost_limit / Estimated_match_error_cost_limit_sum * 
          0.4 * REQ_cost_limit ) )
end (* fun match_error_update_and_estimate *)
      
fun update_req_cost_limit_sum( 
      { current_req_cost_limit_sum, ... } : req_match_error_data,
      First_call : bool,
      First_run : bool,
      REQ_cost_limit : real
      ) : unit =
  if First_call andalso First_run then
    current_req_cost_limit_sum := !current_req_cost_limit_sum + REQ_cost_limit
  else
    ()
      
fun print_req_match_error_data (
      { last_req_cost_limit_sum,
        last_match_error_cost_limit_sum,
        current_req_cost_limit_sum,
        current_match_error_cost_limit_sum 
        } : req_match_error_data ) : unit = (
  p"\nlast_req_cost_limit_sum = "; print_real last_req_cost_limit_sum;
  p"\nlast_match_error_cost_limit_sum = "; 
    print_real last_match_error_cost_limit_sum;
  p"\ncurrent_req_cost_limit_sum = "; print_real( !current_req_cost_limit_sum );
  p"\ncurrent_match_error_cost_limit_sum = "; 
    print_real( !current_match_error_cost_limit_sum );
  nl() )








end (* structure REQ_lib *)
