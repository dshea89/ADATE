(*
  File: random_sampling.sml
  Created 1999-10-21.
  Modified 1999-10-21.
*)

structure Random_sampling : 
sig

type 'a data
val mk_data : int -> 'a data
val receive : 'a data * 'a -> unit
val to_list : 'a data -> 'a list

end =
struct

open Lib

structure H = Int_HashTable

(* Similar to type data0 in req_lib6.sml (structure Random_ladder). *)
type 'a data = {
  n_received : real ref,
  max_sample_card : int,
  sample : 'a H.hash_table
  }

exception Random_sampling_exn

fun mk_data( N : int ) : 'a data = {
  n_received = ref 0.0,
  max_sample_card = N,
  sample = H.mkTable( 10, Random_sampling_exn )
  }

(* Copied from structure Random_ladder in req_lib6.sml: *)

fun receive( { n_received, max_sample_card, sample } : 'a data, 
             X : 'a ) : unit =
  let
    val () = real_inc n_received
    val N = H.numItems sample
  in
    if N < max_sample_card then 
      H.insert sample ( N+1, X )
    else if randReal() < real N / !n_received then
      let
        val I = randRange( 1, N )
      in
        H.remove sample I;
        H.insert sample ( I, X )
      end
    else
      ()
  end

fun to_list( { sample, ... } : 'a data ) : 'a list = H.listItems sample



end (* structure Random_sampling *)







