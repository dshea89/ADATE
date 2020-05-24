(*
  File: heap.sml
  Taken out from lib.sml 1998-04-21.
*)
signature ELEM_TYPE_AND_LESS = 
sig 
  type elem
  val < : elem*elem-> bool
end

signature HEAP =
sig
  type elem
  type heap
  val heap_nil : heap
  val heap_insert : elem*heap -> heap
  val heap_delete_min : heap -> (elem*heap) option
  val heap_size : heap -> int
  val heapify : elem list -> heap
  val heap_report : heap -> elem list
  val heap_sort : elem list -> elem list
  val n_max : int * elem list -> elem list
end
 
functor Heap_functor( Elem_type_and_less : ELEM_TYPE_AND_LESS ) : HEAP =
struct

datatype 'a bin_tree = bt_nil | bt_cons of 'a * 'a bin_tree * 'a bin_tree

(* An applicative heap is an int * elem bin_tree pair where the int 
  is the no of elements in the heap which is used to find the right-most leaf.
*)
open Elem_type_and_less

type heap = int * elem bin_tree

(*
fun ok(bt_cons(_,bt_nil,bt_nil)) = true
  | ok(bt_cons(_,bt_nil,bt_cons(_,_,_))) = false
  | ok(bt_cons(Ro,bt_cons(RoLe,bt_nil,bt_nil),bt_nil)) = Ro<=(RoLe:int)
  | ok(bt_cons(_,bt_cons(_,_,_),bt_nil)) = false
  | ok(bt_cons(Ro, Le as bt_cons(RoLe,LeLe,RiLe),
                   Ri as bt_cons(RoRi,LeRi,RiRi))) =
  Ro<=RoLe andalso Ro<=RoRi andalso ok Le andalso ok Ri
*)

local
exception To_path
fun to_path' 1 = nil
  | to_path' N = (N mod 2 <> 0) :: to_path'(N div 2)
in
fun to_path N = if N<=0 then raise To_path else rev(to_path' N)
end

val heap_nil = (0,bt_nil)
fun heap_size(N,_) = N


local
fun heap_insert(X,(nil,bt_nil)) = bt_cons(X,bt_nil,bt_nil)
  | heap_insert( X, (Right::Path,bt_cons(RoXs,LeXs,RiXs)) ) =
  if Right then
    case heap_insert(X,(Path,RiXs)) of
      RiXs as bt_cons(RoRiXs,LeRiXs,RiRiXs) =>
    if RoRiXs < RoXs then
      bt_cons( RoRiXs, LeXs, bt_cons(RoXs,LeRiXs,RiRiXs) )
    else
      bt_cons(RoXs,LeXs,RiXs)
  else
    case heap_insert(X,(Path,LeXs)) of 
      LeXs as bt_cons(RoLeXs,LeLeXs,RiLeXs) =>
    if RoLeXs < RoXs then
      bt_cons( RoLeXs, bt_cons(RoXs,LeLeXs,RiLeXs), RiXs )
    else
      bt_cons(RoXs,LeXs,RiXs)
in (* local *)

val heap_insert = fn(X,(N,Xs)) => (N+1,heap_insert(X,(to_path(N+1),Xs)))

end (* local *)

fun delete_last( nil, bt_cons(RoXs,bt_nil,bt_nil) ) = (RoXs,bt_nil)
  | delete_last(Right::Path,bt_cons(RoXs,LeXs,RiXs)) =
  if Right then
    case delete_last(Path,RiXs) of (Last,RiXs) =>
      ( Last, bt_cons(RoXs,LeXs,RiXs) )
  else
    case delete_last(Path,LeXs) of (Last,LeXs) =>
      ( Last, bt_cons(RoXs,LeXs,RiXs) )

exception Sift_down of elem bin_tree
fun sift_down(RoXs,bt_nil,bt_nil) = bt_cons(RoXs,bt_nil,bt_nil)
  | sift_down( Xs as (RoXs,bt_cons(RoLeXs,bt_nil,bt_nil),bt_nil) ) =
  if RoLeXs < RoXs then
    bt_cons( RoLeXs, bt_cons(RoXs,bt_nil,bt_nil), bt_nil )
  else
    bt_cons Xs
  | sift_down( Xs as (RoXs, LeXs as bt_cons(RoLeXs,LeLeXs,RiLeXs), 
                            RiXs as bt_cons(RoRiXs,LeRiXs,RiRiXs)) ) =
  let fun left() = bt_cons( RoLeXs, sift_down(RoXs,LeLeXs,RiLeXs), RiXs )
      fun right() = bt_cons( RoRiXs, LeXs, sift_down(RoXs,LeRiXs,RiRiXs) )
  in
    if RoLeXs < RoXs then
      if RoRiXs < RoLeXs then right() else left()
    else if RoRiXs < RoXs then
      if RoLeXs < RoRiXs then left() else right()
    else
      bt_cons Xs
  end
  handle Match => raise Sift_down(bt_cons Xs)

local
fun heap_delete_min(nil,bt_cons(RoXs,bt_nil,bt_nil)) = (RoXs,bt_nil)
  | heap_delete_min(Path,Xs) =
  case delete_last(Path,Xs) of  ( Last, bt_cons(RoXs,LeXs,RiXs) ) =>
    ( RoXs, sift_down(Last,LeXs,RiXs) )
in

val heap_delete_min = fn(N,Xs) => 
  if N=0 then
    NONE
  else
    case heap_delete_min(to_path N,Xs) of (Min,Rest) =>
    SOME(Min,(N-1,Rest))

end (* local *)

exception Bad_del_min_arg of heap

fun heap_report(N,Xs) =
  case heap_delete_min(N,Xs) of
    NONE => nil
  | SOME(Min,Rest) => 
    Min::heap_report Rest

fun hr_test(N,Xs) = (case heap_report(N,Xs) of _ => (N,Xs))
  handle Bad_del_min_arg H => H

exception Bad_insert_arg of int * heap

fun heapify( Xs : elem list ) =
  case Xs of nil => (0,bt_nil)
  | X1::Xs1 => heap_insert(X1,heapify Xs1) 

fun heap_sort Xs = heap_report(heapify Xs)
  
val Test =  [6,1,3,9,5,3,1,2,6,8,9]

exception N_max_exn
fun n_max( N : int, Xs : elem list ) : elem list =
  if Int.<( N, 0 ) then 
    raise N_max_exn
  else if N = 0 then
    []
  else
  let
    val H = ref heap_nil
    fun insert X = (
      H := heap_insert( X, !H );
      if Int.>( heap_size( !H ), N ) then
        case heap_delete_min( !H ) of SOME( _, H' ) => H := H'
      else
        ()
      )
  in
    List1.loop( insert, Xs );
    heap_report( !H ) 
  end
       
    





end (* functor Heap_functor *)
