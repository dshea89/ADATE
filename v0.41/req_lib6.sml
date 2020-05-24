(* File: req_lib6.sml.
   Created 1999-05-12.
   Modified 1999-05-14.
*)

functor Random_ladder(
(* Not to be compared with functor Ladder in req_lib3.sml. *)
    Random_ladder_arg :
      sig
        type eval_type
      end ) :
sig
  type data0
  type data1
  type data2
  val mk_data : unit -> data0

  val receive : data0 * Random_ladder_arg.eval_type -> unit
  (* Random sampling of the eval values produced during the first run. *)

  val build_ladder1 : data0 * ( Random_ladder_arg.eval_type -> real list ) -> 
        data1
  (* Builds a ladder (not the same as ladder in req_lib3.sml!) of real list
     values shortened so much that they barely can be separated in order to
     save space.  *)

  val filter_ladder1 : data1 * int * ( Random_ladder_arg.eval_type -> bool ) ->
        data1
  (* Removes eval values occurring in Merged_map.
     In the data object, n_received is decreased by the number of eval values 
     represented by Merged_map.  *)

  val ladder1_min : data1 -> real list
  (* Returns the best order no. *)

  val cumulate : data1 -> data2
  (* Builds ladder2 from ladder1. Sets ladder1 to nil *)

  val order_no : data2 * real list -> int

end =
struct
open SplayTree Lib List1 Ast Ast_lib Random_ladder_arg

structure H = Int_HashTable


type data0 = {
  n_received : int ref,
  sample : eval_type H.hash_table (* Hash table used for random selection. *)
  }

type data1 = {
  n_received : int ref,
  ladder1 : ( eval_type * real list ) list
  }

type data2 = { ladder2 : ( real list * int ref ) splay ref }

exception Sample_exn

fun mk_data( () ) : data0 = {
  n_received  = ref 0,
  sample = H.mkTable( 100, Sample_exn )
  }


fun receive( { n_received, sample } : data0, 
             Eval : eval_type ) : unit =
  let
    val () = inc n_received
    val N = H.numItems sample
  in
    if N < Constants.Total_max_REQ_storage then 
      H.insert sample ( N+1, Eval )
    else if randReal() < real N / real( !n_received ) then
      let
        val I = randRange( 1, N )
      in
        H.remove sample I;
        H.insert sample ( I, Eval )
      end
    else
      ()
  end

fun cmp( Xs, Ys ) = list_compare( Real.compare, Xs, Ys )


exception Truncate_real_lists_exn
fun shorten_real_lists( Xss : real list list ) : real list list =
  case Xss of
    [] => Xss
  | [ _ ] => Xss
  | [ _, _ ] => Xss
  | Xs1 :: Xs2 :: Xs3 :: Xss =>
  let
    val N = max2( op<,
             length( longest_common_prefix'( real_rep_eq, [ Xs1, Xs2 ] ) ),
             length( longest_common_prefix'( real_rep_eq, [ Xs2, Xs3 ]  ) ) )

    val L = length Xs2

    val Xs2 = 
      if N > L then
        raise Truncate_real_lists_exn
      else if N = L then
        Xs2
      else
        take( N+1, Xs2 )
  in
    Xs1 :: shorten_real_lists( Xs2 :: Xs3 :: Xss )
  end
      
structure S = Splay_lib

fun build_ladder1( 
      { n_received, sample } : data0, 
      merged_order_no : eval_type -> real list 
      ) : data1 =
let
  val Evals = H.listItems sample
  val Evals_and_order_nos =
    map( fn Eval => ( Eval, merged_order_no Eval ), Evals )
  val Evals_and_order_nos =
    cmpsort( fn( ( _, No1), (_,No2) ) => cmp( No1, No2 ), Evals_and_order_nos )

  val Evals = map( #1, Evals_and_order_nos )
  val Order_nos = map( #2, Evals_and_order_nos )
  val Order_nos = shorten_real_lists Order_nos
in { 
  n_received  = ref( !n_received ),
  ladder1 = combine( Evals, Order_nos )
  }
end (* build_ladder1 *)



fun filter_ladder1( 
      { n_received, ladder1 } : data1, 
      N_req_pq_eval_pq_prefix : int,
      keep : eval_type -> bool ) : data1 = { 
  n_received = ref( !n_received - N_req_pq_eval_pq_prefix ),
  ladder1 = filter( fn( E, _ ) => keep E, ladder1 )
  }

fun ladder1_min( { ladder1 : ( eval_type * real list ) list, ... } : data1 )
    : real list =
  case ladder1 of 
    nil => [ 1.0E200 ]
  | ( _, Order_no ) :: _ => Order_no


fun cumulate( { n_received, ladder1 } : data1 ) : data2 =
let
  val Order_nos = map( #2, ladder1 )
  val N_evals_per_step : real = 
    real( !n_received ) / real( length Order_nos + 1 )
  
  val So_far = ref( ~N_evals_per_step )
  val Ladder2_list = map( fn Xs => (
    So_far := !So_far + N_evals_per_step;
    ( Xs, ref( Real.round( !So_far ) ) ) ),
    Order_nos )
in 
  { ladder2 = ref( S.fromList Ladder2_list ) }
end (* fun cumulate *)

val cmp = fn( (No1 : real list,_), (No2,_) ) => cmp( No1, No2 )
   
fun order_no( 
      { ladder2 } : data2,
      Merged_order_no : real list
      ) : int =
  case !ladder2 of
    SplayNil => 1
  | _ =>
  let
    val ( ( No, So_far : int ref ), L ) =
      case S.glb( cmp, ( Merged_order_no, ref Max_int ), !ladder2 ) of
        ( NONE, L ) => S.min( cmp, L )
      | ( SOME Step, L ) => ( Step, L )
  in
(*
    p"\nMerged_order_no = "; print_real_list Merged_order_no;
    p"  Matching no = "; print_real_list No;
    p" !So_far = "; p(Int.toString( !So_far ) );
*)
    ladder2 := L;
    inc So_far;
    !So_far
  end


end (* functor Random_ladder *)
