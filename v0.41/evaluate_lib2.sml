(* File: evaluate_lib2.sml.
   Created 1999-10-21.
   Modified 1999-11-02
*)

structure Eval_selection :
sig
type 'a selection_data
(* One quick_eval_value selection_data object for each value 
   in Max_time_distribution. *)

val initial_selection_data : 
  ( real * ( 'a * 'a -> order ) )list -> 'a selection_data
val receive : 'a selection_data * 'a -> unit
val cutoffs : 'a selection_data -> 'a list
(* The return value is stored in the field cutoffs_list in each individual
   just after finishing expansion of the individual.
*)
end =
struct
open Lib List1 Ast Ast_lib

(* To be used with 'a = quick_eval_value_type. *)

type 'a selection_data = {

  weights_and_pe_cmps : ( real * ( 'a * 'a -> order ) )list,
(* Typically [ (0.05,pe3_cmp), (0.05,pe2_cmp), (0.1,pe1_cmp) ]. A 'a object
   rejected by the first pe_cmp in this list moves on to the second and  so on.
   Due to this pipelining, order is important.
*)

  sample : 'a Random_sampling.data
  }

fun initial_selection_data( Weights_and_pe_cmps )
    : 'a selection_data = {
  weights_and_pe_cmps = Weights_and_pe_cmps,
  sample = Random_sampling.mk_data Constants.Eval_sample_card
  }

fun receive( S : 'a selection_data, X : 'a ) : unit =
  Random_sampling.receive( #sample S, X )

exception Cutoff_exn
fun cutoff( Weight : real, Pe_cmp : 'a * 'a -> order, Sample : 'a list ) 
    : 'a * 'a list =
let
  val Sample = cmpsort( Pe_cmp, Sample )
  (* Best values first. *)
  val N = length Sample
  val Last_good = floor( Weight * real N )
in
  ( nth( Sample, Last_good ), drop( Last_good+1, Sample ) )
end
handle Ex => (
  p"\ncutoff:\n";
  p"\nWeight = "; print_real Weight;
  p"\nN = "; print_int(length Sample);
  p"\nLast_good = "; print_int( floor( Weight * real(length Sample ) ) );
  raise Cutoff_exn )

fun cutoffs( { weights_and_pe_cmps, sample } : 'a selection_data ) : 'a list =
let
  fun g( Sample_left, Weights_and_pe_cmps ) =
    case Weights_and_pe_cmps of
      [] => []
    | ( Weight, Pe_cmp ) :: Weights_and_pe_cmps =>
    let
      val ( Cutoff, Sample_left ) = cutoff( Weight, Pe_cmp, Sample_left )
    in
      Cutoff :: g( Sample_left, Weights_and_pe_cmps )
    end
in
  g( Random_sampling.to_list sample, weights_and_pe_cmps )
end
  

end (* structure Eval_selection *)

