(* File: genealogical_search_lib.sml.
   Created 1996-01-30.
   Modified 1997-12-08.
*)
signature ID =
sig

type id = word * word
val gen_id : unit -> id
val current_id : unit -> id
val set_id : id -> unit
val hashVal : id -> word
structure Id_HashTable : MONO_HASH_TABLE
val toString : id -> string
val fromString : string -> id option
val id_pack : id -> string
val id_unpack : string -> id
val < : id * id -> bool

end

structure Id : ID =
struct
open Lib 

type id = word * word

local

val Current_id_no = ref( Word.fromInt 0 ) 
val Current_id_no' = ref( Word.fromInt 0 )

in

exception Gen_id
fun gen_id() : id =   ( 
  word_inc Current_id_no;
  if Word.>=( !Current_id_no, Lib.Max_word ) then (
    Current_id_no := Word.fromInt 0;
    word_inc Current_id_no';
    if Word.>=( !Current_id_no', Lib.Max_word ) then 
      raise Gen_id 
    else 
      ()
    )
  else
    ();
  ( !Current_id_no', !Current_id_no )
  )

fun current_id() : id = ( !Current_id_no', !Current_id_no )

fun set_id( X, Y ) = (
  Current_id_no' := X;
  Current_id_no := Y
  )

end (* local *)


structure Id_hash_key =
struct
  type hash_key = id
  fun hashVal( M, N ) = Word.xorb( M, N )
  fun sameKey( X, Y : id ) = X = Y
end

val hashVal = Id_hash_key.hashVal

structure Id_HashTable = HashTableFn( Id_hash_key )

fun toString( M, N ) = Word.toString M ^ "_" ^ Word.toString N

fun fromString S = 
  case String.tokens (fn X => X = #"_") S of 
    [ S1, S2 ] => (
      case ( Word.fromString S1, Word.fromString S2 ) of
        ( SOME W1, SOME W2 ) => SOME( W1, W2 )
      | _ => NONE
      )
  | _ => NONE

fun op<( (X1,Y1) : id, (X2,Y2) : id ) : bool =
  Word.<( X1, X2 ) orelse
  ( X1 = X2 andalso Word.<( Y1, Y2 ) )

val id_pack = toString
val id_unpack = fn S => case fromString S of SOME ID => ID

end (* struct *)






signature GENEALOGICAL_SEARCH_LIB =
sig

val Epsilon : real

val update_bests : 
  ( 'a * 'a  -> order ) *
  ( 'a * 'a  -> order ) *
  ( 'a -> 'a ) *
  'a *
  'a SplayTree.splay -> 'a list * 'a SplayTree.splay
 
val update_bests_check : 
  ( 'a * 'a  -> order ) *
  ( 'a * 'a  -> order ) *
  'a *
  'a SplayTree.splay -> bool
 
val rand_select : ('a -> real) *  int * 'a list  -> 'a list

type 'a synt_compl_matches = ( real * real * 'a option ) list
val scm_out : Lib.outstream * (Lib.outstream * 'a -> unit) * 
      'a synt_compl_matches -> unit
val create_scm_class : '1a * ('1a -> real) * int * real -> 
      '1a synt_compl_matches ref

(* For use with targets randomized per class: *)
val create_scm_class_with_random_targets 
    : '1a * ('1a -> real) * int -> '1a synt_compl_matches ref

val scm_update : real * 'a * 'a synt_compl_matches ->
      'a synt_compl_matches option * 'a option 
val scm_update_check : real * 'a * 'a synt_compl_matches -> bool
val scm_indis : 'a synt_compl_matches -> 'a list

type '1a lcs_class
val lcs_class_out : 
  Lib.outstream * (Lib.outstream * '1a -> unit) * '1a lcs_class -> unit
val create_lcs_class : '1a * ('1a -> real) * int * real -> '1a lcs_class
val init_lcs_class : ('1a -> Id.id) * ('1a -> bool) *
      ({ancestor_evals : '1b, other : '1a} -> int) *
      '1a * '1b * '1a lcs_class -> unit
val update_lcs_class 
    : ('1a -> Id.id) * ('1a -> real) * '1a lcs_class * '1a -> '1a option
val update_lcs_class_check 
    : ('1a -> Id.id) * ('1a -> real) * '1a lcs_class * '1a -> bool
val end_lcs_class : ('1a -> Id.id) * '1a lcs_class -> '1a option
val lcs_class_indis : '1a lcs_class -> '1a list
val all_lcs_class_indis : '1a lcs_class -> '1a list

type '1a output_class = '1a * int * '1a list ref
val create_output_class : '1a * int -> '1a output_class
val update_output_class : 
  ( '1a -> real ) * ( '1a -> real ) * '1a output_class * '1a -> '1a option
val update_output_class_check : 
  ('1a -> Id.id) * ( '1a -> real ) * ( '1a -> real ) * '1a output_class * '1a 
  -> bool
val output_class_indis : '1a output_class -> '1a list
val output_class_base : '1a output_class -> '1a
val output_class_out : ( '1a -> real ) * ( '1a -> real ) *
  Lib.outstream * (Lib.outstream * '1a -> unit) * '1a output_class -> unit

end (* sig *)


structure Genealogical_search_lib : GENEALOGICAL_SEARCH_LIB =
(* Only contains code of general nature that does not depend on Spec. *)
struct
open Lib List1 Ast Ast_lib Print Parse 

val Epsilon = 1.0E~6



local

open LibBase SplayTree Splay_lib

in

fun update_bests( 
      eval_cmp : 'a * 'a -> order,
      synt_compl_cmp : 'a * 'a -> order,
      dummy_class_to_class : 'a -> 'a,
      X : 'a,
      Xs : 'a splay ) : 'a list * 'a splay =
(* Returns ( Knocked out classes, New Xs ).
   X is inserted only if its eval GLB has greater syntactic complexity.
*)
  let
    val ( Proceed, Xs ) =
      case glb( eval_cmp, X, Xs ) of
        ( NONE, Xs ) => ( true, Xs )
      | ( SOME Y, Xs ) =>
      case synt_compl_cmp( X, Y ) of
        LESS => ( true, Xs )
      | EQUAL => ( false, Xs )
      | GREATER => ( false, Xs )
  in
    if not Proceed then
      ( [ X ], Xs )
    else
  let
    fun del Xs =
      case lub( eval_cmp, X, Xs ) of
        ( NONE, Xs ) => ( [], Xs )
      | ( SOME Y, Xs ) =>
      case synt_compl_cmp( X, Y ) of
        GREATER => ( [], Xs )
      | _ =>
      case delete( eval_cmp, Y, Xs ) of
        Xs =>
      case del Xs of
        ( Knocked_out, Xs ) => ( Y :: Knocked_out, Xs )
    val ( Knocked_out, Xs ) = del Xs
  in
    ( Knocked_out, insert( eval_cmp, dummy_class_to_class X, Xs ) )
  end
  end (* update_bests *)

local

val Eval_cmp_timer = mk_timer "Eval_cmp_timer"
val N = ref 0.0
val Last_print_time = ref 0.0

in

fun update_bests_check( 
      eval_cmp : 'a * 'a -> order,
      synt_compl_cmp : 'a * 'a -> order,
      X : 'a,
      Xs : 'a splay ) : bool = 
let
  val () = N := !N + real(no_of_nodes Xs)
  val () = start_timer Eval_cmp_timer
  val Y =
  case glb( eval_cmp, X, Xs ) of
    ( NONE, Xs ) => true
  | ( SOME Y, Xs ) =>
  case synt_compl_cmp( X, Y ) of
    LESS => true
  | EQUAL => false
  | GREATER => false
  val () = stop_timer Eval_cmp_timer
  val T = check_timer Eval_cmp_timer
in
  if T - !Last_print_time > 100.0 then (
    Last_print_time := T;
    p"\n\nupdate_bests_check:\n";
    p"  Total no of nodes = "; print_real( !N );
    p"\n  No of nodes in Xs = "; print_int( no_of_nodes Xs );
    p"\n  Total eval cmp time = "; print_real T; nl(); nl() )
  else
    ();
  Y
end

end (* local *)

   
(*
(* Test code: *)

local

fun b( (Ev, Sy), Le, Ri ) = 
  SplayObj{ value = ( Ev, Sy ), left = Le, right = Ri }

fun l( Ev, Sy ) =
  SplayObj{ value = ( Ev, Sy ), left = SplayNil, right = SplayNil }

in

val Xs =
  b( ( ~30, 92.7 ),
    b( ( ~50, 120.5 ),
      l( ~60, 127.3 ),
      l( ~40, 108.4 ) ),
    l ( ~20, 58.1 ) )

fun eval_cmp( ( Ev1 : int, _ ), ( Ev2, _ ) ) = 
  if Ev1 < Ev2 then
    LESS
  else if Ev1 > Ev2 then
    GREATER
  else
    EQUAL

fun synt_compl_cmp( ( _, Sy1 : real ), ( _, Sy2 ) ) =
  if Sy1 < Sy2 then
    LESS
  else if Sy1 > Sy2 then
    GREATER
  else
    EQUAL

fun dummy_class_to_class( E, S ) = ( E, S+0.0000001 )

val Indi = ( ~15, 64.8 )

val Update = 
  update_bests_check( eval_cmp, synt_compl_cmp, Indi, Xs )
val ( Knocked_out, Ys ) = 
  update_bests( eval_cmp, synt_compl_cmp, dummy_class_to_class, Indi, Xs )

fun node_out( out, ( Ev, Sy ) ) =
  output( out, Int.toString Ev ^ " " ^ Real.toString Sy )

val _ = (
  splay_out( !std_out, node_out, Xs );
  output( !std_out, "\n\nUpdate = " ^ Bool.toString Update ^ "\n\n" );
  list_out( !std_out, node_out, Knocked_out );
  output( !std_out, "\n\n" );
  splay_out( !std_out, node_out, Ys )
  )

end (* local *)
*)


end (* local *)



exception Pick_closest
fun pick_closest( r : 'a -> real, W : real, Xs : 'a list ) : 'a * 'a list =
  case Xs of
    [] => raise Pick_closest
  | X1::Xs1 => 
  if W <= r X1 then (X1,Xs1) else
  case Xs1 of
    [] => (X1,Xs1)
  | X2::Xs2 => 
  if W <= r X2 then
    if W - r X1 < r X2 - W then (X1,Xs1) else (X2,X1::Xs2)
  else
    case pick_closest(r,W,Xs1) of (Z,Zs) => (Z,X1::Zs)


local

val Rand = Random.rand( 810361039, 719459918 )


in

exception Rand_select
fun rand_select( r : 'a -> real, N : int,  Xs : 'a list ) :  'a list =
  if N<=0 then 
    [] 
  else if N >= length Xs then
    Xs
  else
  let
    val Xs = sort (fn(X,Y) => r X < r Y) Xs
    val Lower = r(hd Xs)
    val Upper = r(dh Xs)
    val _ = if Upper<Lower then raise Rand_select else ()
    fun gen_rand() = Lower + Random.randReal Rand * (Upper-Lower)
    fun g(N,Ys) =
      if N=0 then
        []
      else
        case pick_closest(r,gen_rand(),Ys) of (Z,Zs) => Z :: g(N-1,Zs)
  in
    g(N,Xs)
  end (* rand_select *)

end (* local *)





(* Code related to LCS diversity. *)


exception To_be_replaced1
exception To_be_replaced2
exception To_be_replaced3
fun to_be_replaced( find_id : 'a -> Id.id,
                    dist : {ancestor_evals : '1b, other : 'a} -> int,
                    Base : 'a,
                    Ancector_evals : '1b,
                    Olds : 'a list,
                    Dists : (int * Id.id * Id.id) list
                    ) 
    : (Id.id option * (int * Id.id option * Id.id option) list) list * bool =
  if length Dists <> length Olds * (length Olds -1 ) div 2 then
    raise To_be_replaced2
  else if not(exists(fn X => find_id X = find_id Base, Olds)) then
    raise To_be_replaced3
  else
  let
    fun id_option_less(NONE,_) = false
      | id_option_less(SOME Id, NONE) = true
      | id_option_less(SOME Id1, SOME Id2) = Id.<( Id1, Id2 )
    val Dists = map( fn(Dist,X,Y) => (Dist, SOME X, SOME Y), Dists)
    val Add_dists = map( fn X => 
      (dist{ancestor_evals=Ancector_evals,other=X}, NONE, SOME(find_id X)), 
      Olds)
    val Expanded_dists as (D,_,_) :: _ =
      sort (fn((D1,_,_),(D2,_,_)) => D1<D2) (Add_dists@Dists)
    val Removal_candidates = takewhile( fn(D',_,_) => D' = D, Expanded_dists )
    val Removal_candidates = fast_make_set(id_option_less, filter( fn X
      => X <> SOME(find_id Base),
        flat_map( fn(_,X,Y) => [X,Y], Removal_candidates ) ))
    val New_distss = 
      map( fn X =>
        filter( fn(_,Y,Z) => X <> Y andalso X <> Z, Expanded_dists ),
        Removal_candidates )
    fun dists_less(Dists1,Dists2) =
        list_less( fn((D1,_,_),(D2,_,_)) => D1<D2, Dists1,Dists2 )
    val New_dists::New_distss = rev(sort dists_less New_distss)
    val New_distss = takewhile( fn Dists => not(dists_less(Dists,New_dists)),
                                New_dists::New_distss )
    val Newss = map( fn New_dists =>
      fast_make_set( id_option_less,
        flat_map( fn(_,X,Y) => [X,Y], New_dists ) ),
      New_distss)
    val Diffs = map( fn News =>
      difference( map(fn X => SOME(find_id X),Olds), News ), 
      Newss )
    val Cands = map( fn([X],New_dists) => (X,New_dists),
      filter( fn(Xs,_) => not(null Xs), combine(Diffs,New_distss) ) )
    val Equal = exists(null,Diffs) (* Replacing a Cand in Cands doesn't 
          improve the distance measure if Equal is true. *)
  in
    (Cands,Equal)
  end (* to_be_replaced *)


(*
fun test( Base : Id.id*int, Parent : Id.id*int, Olds : (id*int) list ) =
  let
    fun find_id(X,Y) = X
    fun dist {parent : Id.id*int, other : Id.id*int} = abs(#2 parent - #2 other)
    val Olds = Base::Olds
    val Dists =
      map( fn(X,Y) => ( dist{parent=X,other=Y}, find_id X, find_id Y ),
        filter(fn((X,_),(Y,_)) => X<Y, cart_prod(Olds,Olds)) )
  in
    to_be_replaced( find_id, dist, Base, Parent, Olds, Dists )
  end

val T1 =  test( (77,7), (100,10), [ (10,1), (20,2), (50,5) ] );
val T2 =  test( (77,7), (100,10), [ (~1,0), (10,1), (20,2), (50,5) ] );
val T3 =  test( (77,7), (100,10), [ (~1,0), (40,4), (90,9) ] );
val T4 =  test( (77,7), (100,10), [ (10,1), (20,2), (90,9), (110,11) ] );
val T5 =  test( (77,7), (300,30), [ (~1,0), (10,1), (70,7), (80,8), (120,12) ] );
val T6 =  test( (77,7), (10,1), [ (11,1), (12,1), (13,1), (14,1) ] );
val T7 =  test( (77,7), (15,1), [ (11,1), (12,1), (13,1), (14,1) ] );
val T8 =  test( (77,7), (11,1), [ (10,1), (20,2), (30,3), (40,4) ] );
val T9 =  test( (77,7), (21,2), [ (10,1), (20,2), (30,3), (40,4) ] );
val T10 =  test( (77,7), (31,3), [ (10,1), (20,2), (30,3), (40,4) ] );
val T11 =  test( (77,7), (41,4), [ (10,1), (20,2), (30,3), (40,4) ] );
val T12 =  test( (77,7), (150,15), [ (10,1), (30,3), (50,5), (170,17), (190,19), (210,21) ]);
val T13 =  test( (10,1), (30,3), [ (20,2),  (40,4), (50,5), (60,6) ] );
*)



structure H = Lib.Int_HashTable
  
exception Fast_rem_dupss
fun fast_rem_dupss( key_sel :  'a -> int, Xss : 'a list list ) : 'a list list =
  let
    val Table : unit H.hash_table = 
      H.mkTable( 2 * int_sum(map(length,Xss)), Fast_rem_dupss )
    fun g Xss =
      case Xss of
        nil => nil
      | Xs1::Xss1 =>
          filter( fn X =>
            case H.find Table (key_sel X) of
              NONE => (
                H.insert Table ((key_sel X),());
                true )
            | SOME () => false,
            Xs1 ) :: g Xss1
  in
    g Xss
  end

(*
val Test = fast_rem_dupss(fn X => X, [ [1,2,3,4], [5,3,6,7,4,8], [9,10,7,4] ])
*)




(* Code related to syntactic complexity proximity selection *)

type 'a synt_compl_matches = ( real * real * 'a option ) list
(* ( Target_synt_compl, Actual_synt_compl, Individual_option ) list
  Actual_synt_compl for NONE is assumed to be Max_real.
*)

fun scm_eq( indi_eq : 'a * 'a -> bool, Xs : 'a synt_compl_matches,
      Ys : 'a synt_compl_matches ) : bool =
  list_eq( fn( (Target1,Actual1,Indi_opt1), (Target2,Actual2,Indi_opt2) ) =>
    real_rep_eq( Target1, Target2 ) andalso real_rep_eq( Actual1, Actual2 ) 
    andalso
    option_eq( indi_eq, Indi_opt1, Indi_opt2 ),
    Xs, Ys )




exception Create_scm_class
fun create_scm_class( 
      Base: '1a, 
      synt_compl : '1a -> real,
      Max_scm_class_card : int,
      Synt_compl_ratio : real ) : '1a synt_compl_matches ref =
  case synt_compl Base of Base_synt_compl =>
  if Base_synt_compl < 0.0 orelse 
     Synt_compl_ratio < 1.0 orelse Synt_compl_ratio > 2000.0 then
    raise Create_scm_class
  else 
    ref( map( fn I =>
      ( Base_synt_compl * real_pow(Synt_compl_ratio,real I), 
        Max_real, NONE ),
      fromto(1,Max_scm_class_card) ) )


exception Create_scm_class_with_targets
fun create_scm_class_with_random_targets( 
      Base: '1a, 
      synt_compl : '1a -> real,
      Seed : int ) : '1a synt_compl_matches ref =
let
  val Seed' = Seed
  val Base_synt_compl = synt_compl Base
  val Seed = ( real Seed + 1.5434535E10 ) * Base_synt_compl
  val Rand = Random.rand( hash_real_to_int Seed, 44355697 )

  val () = loop( fn _ => 
    Random.randReal Rand, fromto( 0, abs(Seed' mod 2719 ) ) )
  val T1 = Base_synt_compl + Random.randReal Rand* ( Base_synt_compl + 10.0 )
  val T2 = Base_synt_compl + 
    Random.randReal Rand * ( 10.0 * Base_synt_compl + 100.0 )

  val Targets = [ T1, T2 ]
  val Min_target = min( op<, Targets )
in
  if Base_synt_compl < 0.0 orelse  Min_target < Base_synt_compl - 0.001 then
    raise Create_scm_class_with_targets
  else 
    ref( map( fn Target => ( Target, Max_real, NONE ), sort (op<) Targets ) )
end



fun scm_out( out, indi_out : outstream * 'a -> unit,
      Xs : 'a synt_compl_matches ) : unit =
  let
    fun p S = output(out,S);
    fun elem_out(Target,Actual,Indi_opt) = (
      p( "Target = " ^ Real.toString Target ^ "    " );
      p( "Actual = " ^ Real.toString Actual ^ "\n");
      case Indi_opt of
        NONE => p "NONE\n\n"
      | SOME Indi => (indi_out(out,Indi); p"\n\n")
      )
  in
    map(elem_out,Xs);
    ()
  end

exception Scm_less1
exception Scm_less2
fun scm_less( Xs : 'a synt_compl_matches, Ys : 'a synt_compl_matches )
    : bool =
  if length Xs <>  length Ys then
    raise Scm_less1
  else
  let
    fun f Zs = filter( fn(_,_,NONE) => false | _ => true, Zs )
    val Xs = f Xs
    val Ys = f Ys
    val _ = if length Xs <> length Ys then raise Scm_less2 else ()
    fun sq_sum Zs = real_sum(map( fn(T,A,_) => (T-A)*(T-A), Zs ))
  in
    sq_sum Xs < sq_sum Ys - Epsilon
  end

(* Test: *)

val Xs = [ (10.0,11.0,SOME"B"), (20.0,25.0,SOME"C"), (30.0,28.0,SOME"D") ]
val Ys = [ (10.0,11.0,SOME"B"), (20.0,27.0,SOME"C"), (30.0,28.0,SOME"D") ]
val Zs = [ (10.0,10.5,SOME"B"), (20.0,27.0,SOME"C"), (30.0,28.0,SOME"D") ]
val Tests = [  
  scm_less(Xs,Ys), 
  scm_less(Ys,Xs), 
  scm_less(Xs,Zs), 
  scm_less(Zs,Xs),
  scm_less(Xs,Xs)
  ]
    

exception Scm_update
fun scm_update( Actual : real, Indi : 'a, Xs : 'a synt_compl_matches )
    : 'a synt_compl_matches option * 'a option =
  if null Xs then
    ( NONE, SOME Indi )
  else
  let val Zs = map( fn( Index, (T,A,Indi_opt) ) =>
    ( Index, abs(T-Actual), T, A, Indi_opt ),
    combine( fromto(0,length Xs - 1), Xs ))
  in
  case filter( fn(_,Diff',T,A,_) => Diff'  <  abs(T-A) - Epsilon, Zs ) of
    nil => ( NONE, SOME Indi )
  | Zs =>
  case min( fn((_,Diff1,_,_,_),(_,Diff2,_,_,_)) => Diff1<Diff2, Zs ) of
    ( Index, _, T_repl, A_repl, Indi_repl_opt ) =>
  case list_replace( Xs, Index, (T_repl,Actual,SOME Indi) ) of Ys =>
  case Indi_repl_opt of
    NONE =>  ( SOME Ys, NONE )
  | SOME Indi_repl =>
  case scm_update(A_repl,Indi_repl,Ys) of
    ( NONE, Knocked_out_opt ) => ( SOME Ys, Knocked_out_opt )
  | ( SOME Ws, Knocked_out_opt ) => ( SOME Ws, Knocked_out_opt )
end (* scm_update *)  


fun scm_update_check( Actual : real, Indi : 'a, Xs : 'a synt_compl_matches )
    : bool =
  case scm_update( Actual, Indi, Xs ) of
    ( NONE, _ ) => false
  | _ => true


(*

(* Test: *)

val Tests = [
  scm_update( 10.5, "A",
    [ (10.0,11.0,SOME"B"), (20.0,25.0,SOME"C"), (30.0,28.0,SOME"D") ] ),
  scm_update( 18.0, "A",
    [ (10.0,1.0,SOME"B"), (20.0,35.0,SOME"C"), (30.0,70.0,SOME"D") ] ),
  scm_update( 58.0, "A",
    [ (10.0,1.0,SOME"B"), (20.0,35.0,SOME"C"), (30.0,70.0,SOME"D") ] ),
  scm_update( 58.0, "A",
    [ (10.0,1.0,SOME"B"), (20.0,35.0,SOME"C"), (30.0,Max_real,SOME"D") ] ),
  scm_update( 18.0, "A",
    [ (10.0,1.0,SOME"B"), (20.0,12.0,SOME"C"), (30.0,31.0,SOME"D") ] ),
  scm_update( 18.0, "A",
    [ (10.0,9.0,SOME"B"), (20.0,19.0,SOME"C"), (30.0,31.0,SOME"D") ] )
  ]
*)



type '1a lcs_class = {
  current_scm : '1a synt_compl_matches ref,
  current_dists : (int * Id.id * Id.id) list ref,
  add_dists : (int * Id.id) list ref
    (* Used iff the lcs class isn't full *),
  best_so_far_scm_opt : '1a synt_compl_matches option ref,
  best_so_far_dists : (int * Id.id * Id.id) list ref,
  repl_cands : 
    (Id.id option * (int * Id.id option * Id.id option) list) list ref
  }


fun lcs_class_clone( { current_scm, current_dists, add_dists, 
      best_so_far_scm_opt, best_so_far_dists, repl_cands } : '1a lcs_class )
    : '1a lcs_class =
  {
  current_scm = ref( !current_scm ),
  current_dists = ref( !current_dists ),
  add_dists = ref( !add_dists ),
  best_so_far_scm_opt = ref( !best_so_far_scm_opt ),
  best_so_far_dists = ref( !best_so_far_dists ),
  repl_cands = ref( !repl_cands )
  } 

fun lcs_class_out( out : outstream, indi_out : outstream * '1a -> unit,
      { current_scm,... } : '1a lcs_class ) =
  scm_out(out,indi_out,!current_scm)

fun scm_indis Scm = 
      flat_map( fn(_,_,NONE) => [] | (_,_,SOME Indi) => [Indi], Scm )

fun lcs_class_indis( {current_scm,...} : '1a lcs_class ) =
  scm_indis(!current_scm)

fun all_lcs_class_indis( { current_scm, best_so_far_scm_opt, ... } 
      : '1a lcs_class ) =
  scm_indis(!current_scm) @ (
  case !best_so_far_scm_opt of
    NONE => []
  | SOME Scm => scm_indis Scm )

exception Create_lcs_class
fun create_lcs_class( 
      Base: '1a, 
      synt_compl : '1a -> real,
      Max_lcs_class_card : int,
      Synt_compl_ratio : real ) : '1a lcs_class = {
    current_scm = create_scm_class( Base,  synt_compl, 
      Max_lcs_class_card, Synt_compl_ratio ),
    current_dists = ref nil,
    add_dists = ref nil,
    best_so_far_scm_opt = ref NONE,
    best_so_far_dists = ref nil,
    repl_cands = ref nil
    }


(* To be run on each lcs class just before starting the expansion 
   of the parent: *)
fun init_lcs_class(
      find_id : '1a -> Id.id,
      chosen_parent : '1a -> bool,
      dist : {ancestor_evals : '1b , other : '1a} -> int,
      Base : '1a,
      Ancestor_evals : '1b,
      { current_scm (* in *),
        current_dists (* in *),
        add_dists (* out *),
        best_so_far_scm_opt (* out *),
        best_so_far_dists (* out *),
        repl_cands (* out *)
        } : '1a lcs_class ) : unit =
  if exists( fn(_,_,NONE) => true | _ => false, !current_scm ) then (
    add_dists := map( fn(_,_,SOME Indi) => 
      ( dist{ancestor_evals=Ancestor_evals,other=Indi}, find_id Indi ),
      (~Max_real, ~Max_real,SOME Base) :: 
      filter(   fn(_,_,SOME _) => true | _ => false, !current_scm ) );
    best_so_far_scm_opt := NONE
    )
  else
  let
    val Olds = Base :: map( fn(_,_,SOME Indi) => Indi, !current_scm)
    val (Repl_cands,Equality) =
      to_be_replaced( find_id, dist, Base, Ancestor_evals, Olds, !current_dists)
  in
    best_so_far_scm_opt := (if Equality then SOME(!current_scm) else NONE);
    best_so_far_dists := !current_dists;
    repl_cands := (
      if Equality then
        filter( fn (SOME Id,_) =>
          case filter( fn Indi => find_id Indi = Id, Olds ) of
            [Indi] => not(chosen_parent Indi),
          Repl_cands)
      else
        Repl_cands )
  end (* init_lcs_class *)



(* To be run on each lcs class just after the expansion the parent   
   is finished: *)
fun end_lcs_class( find_id : '1a -> Id.id,
  {current_scm, current_dists, best_so_far_scm_opt,
   best_so_far_dists, ... } : '1a lcs_class ) : '1a option =
  case !best_so_far_scm_opt of
    NONE => NONE
  | SOME Best_so_far_scm => 
  let 
    val Diffs = fast_difference( fn(X,Y) => Id.<( find_id X, find_id Y ),
                  scm_indis(!current_scm), scm_indis(Best_so_far_scm) )
  in
    current_scm := Best_so_far_scm;
    current_dists := !best_so_far_dists;
    case Diffs of
      nil => NONE
    | [Indi] => SOME Indi
  end
      
         
exception Find_knocked_out
fun find_knocked_out(
      find_id : '1a -> Id.id,
      Indi : '1a,
      Current_scm : '1a synt_compl_matches,
      Old_scm_opt : '1a synt_compl_matches option,
      New_scm_opt : '1a synt_compl_matches option
      ) : '1a option =
  case Old_scm_opt of
    NONE => (
      case New_scm_opt of
        NONE => SOME Indi
      | SOME New_scm => (
          case filter( fn(_,_,SOME Indi') => find_id Indi = find_id Indi' 
                       | _ => false, New_scm ) 
          of
            [X] => ()
          | _ => raise Find_knocked_out;
          NONE ) )
  | SOME Old_scm =>
  case New_scm_opt of SOME New_scm =>
  let
    val Old_indis = scm_indis Old_scm
    val New_indis = scm_indis New_scm
    val Current_indis = scm_indis Current_scm
    val Diffs = fast_difference( fn(X,Y) => Id.<( find_id X, find_id Y ),
                  Indi::Old_indis, New_indis@Current_indis )
  in
    case Diffs of
      nil => NONE
    | [Indi] => SOME Indi
  end

  
exception Update_lcs_class1
fun update_lcs_class(
      find_id : '1a -> Id.id,
      synt_compl : '1a -> real,
      { current_scm (* in *),
        current_dists (* in *),
        add_dists (* in *),
        best_so_far_scm_opt (* in/out *),
        best_so_far_dists (* in/out *),
        repl_cands (* in *)
        } : '1a lcs_class,
      Indi : '1a ) :  '1a option =
  (* Returns SOME Indi_repl if Indi_repl was knocked out. *)
  let
    val Old_scm_opt = !best_so_far_scm_opt
    val () =
  if exists( fn(_,_,NONE) => true | _ => false, !current_scm ) then 
    (* The lcs class isn't full. *)
    let 
      val ( SOME New_scm, _ ) = 
        scm_update(synt_compl Indi, Indi, !current_scm)
      val Add_dists = map( fn(Dist,Id) => (Dist, find_id Indi, Id),
                           !add_dists )
    in
      case !best_so_far_scm_opt of
        NONE => ( best_so_far_scm_opt := SOME New_scm;
                  best_so_far_dists := Add_dists @ !current_dists
                  )
      | SOME Best_so_far_scm =>
      if scm_less(New_scm,Best_so_far_scm) then
        ( best_so_far_scm_opt := SOME New_scm;
          best_so_far_dists := Add_dists @ !current_dists
          )
      else
        ()
    end
  else (* The lcs class is full. *)
  if null(!repl_cands) orelse null(!current_scm) then
    ()
  else
  let
    fun id_opt_to_id NONE = find_id Indi
      | id_opt_to_id(SOME Id) = Id
    fun try_repl_cand( Repl_cand : Id.id option, 
      New_dists : (int * Id.id option * Id.id option) list ) =
      let 
        val Repl_cand = id_opt_to_id Repl_cand
        val Current_scm = map( fn X as (Target, Actual, SOME Indi') =>
          if find_id Indi' = Repl_cand then
            (Target,Max_real,NONE)
          else
            X,
          !current_scm)
      in
        case scm_update(synt_compl Indi, Indi, Current_scm) of
          ( NONE, _ ) => raise Update_lcs_class1
        | ( SOME New_scm, _ ) => (New_scm,New_dists)
      end
    val New_scms_and_distss = map( try_repl_cand, !repl_cands )
    val (New_scm,New_dists) = min( fn((X,_),(Y,_)) => scm_less(X,Y),
                                   New_scms_and_distss )
    val New_dists = map( fn(Dist,X,Y) => 
          (Dist, id_opt_to_id X, id_opt_to_id Y),
          New_dists)
  in
    case !best_so_far_scm_opt of
      NONE => ( best_so_far_scm_opt := SOME New_scm;
                best_so_far_dists := New_dists
                )
    | SOME Best_so_far_scm =>
    if scm_less(New_scm,Best_so_far_scm) then (
       best_so_far_scm_opt := SOME New_scm;
       best_so_far_dists := New_dists
       )
    else
      ()
  end
  in
    find_knocked_out( find_id, Indi, !current_scm, Old_scm_opt, 
      !best_so_far_scm_opt )
  end (* update_lcs_class *)


fun update_lcs_class_check(
      find_id : '1a -> Id.id,
      synt_compl : '1a -> real,
      LCS_class as { best_so_far_scm_opt, ... } : '1a lcs_class,
      Indi : '1a ) : bool =
  let
    val Dc = lcs_class_clone LCS_class
    fun indi_eq(X,Y) = find_id X = find_id Y
    fun scm_opt_eq( Xs, Ys ) =
      option_eq( fn(Xs,Ys) => scm_eq( indi_eq, Xs, Ys ), Xs, Ys )
  in
    update_lcs_class( find_id, synt_compl, Dc, Indi );
    not( scm_opt_eq( !best_so_far_scm_opt, !(#best_so_far_scm_opt Dc) ) )
  end




(*

(* Test code: *)

type ti = Id.id * real * int
(* (Id, Synt_compl, Dist_coordinate) *)

fun find_id(Id,_,_) = Id
fun synt_compl(_,Sc,_) = Sc
fun chosen_parent _ = true
fun dist{ ancestor_evals=(_,_,X1:int), other=(_,_,X2)} = abs(X1-(X2-2))
(* Testing convention: Dist coordinate for child always 2 greater than 
   for parent. 
*)

val Base_id = Id.gen_id()
val Base = (Base_id, 100.0, 1000)

val LCS_class : ti lcs_class ref = 
  ref(create_lcs_class(Base,synt_compl,3,1.1))

(* Target synt compls are 110.0, 121.0, 133.1. *)

fun expand( Ancestor_evals : ti, Children : ti list ) = 
  let
    val _ = init_lcs_class( find_id, chosen_parent, dist, Base, 
               Ancestor_evals, !LCS_class )
    val Knocked_outs_checks = 
      map( fn Child => 
        let val Check =
          update_lcs_class_check(find_id,synt_compl,!LCS_class,Child)
        in
          ( Check, 
            update_lcs_class(find_id,synt_compl,!LCS_class,Child) )
        end,
        Children )
    val End_knocked_out_opt = end_lcs_class(find_id,!LCS_class)
  in
  ( !(#current_scm(!LCS_class)), 
    !(#current_dists(!LCS_class)), 
    Knocked_outs_checks,
    End_knocked_out_opt) 
  end


val Ancestor_evals = Base

val Expand = expand( Ancestor_evals, [Base,Base,Base,Base,Base,Base] )

*)


type '1a output_class = '1a * int * '1a list ref

fun output_class_base( Base, _, _ ) = Base

fun output_class_clone( Base, Max_output_class_card, Indis ) =
  ( Base, Max_output_class_card, ref( !Indis ) )

fun create_output_class( Base : '1a, Max_output_class_card : int )
    : '1a output_class =
  ( Base, Max_output_class_card, ref [] )

fun update_output_class(
      fingerprint : '1a -> real,
      synt_compl : '1a -> real,
      ( Base, Max_output_class_card, Indis ) : '1a output_class,
      Indi : '1a ) : '1a option =
  if Max_output_class_card < 1 then
    SOME Indi
  else
  case filter( fn X => real_rep_eq( fingerprint X, fingerprint Indi ), 
         Base :: !Indis ) 
  of
    [ X ] =>
      if synt_compl X < synt_compl Indi + Epsilon then
        SOME Indi
      else if real_rep_eq( fingerprint X, fingerprint Base ) then
        SOME Indi
      else (
        Indis := Indi :: 
          filter( fn X => not( real_rep_eq( fingerprint X, fingerprint Indi )),
            !Indis );
        SOME X )
  | [] =>
  if length( !Indis ) < Max_output_class_card then (
    Indis := Indi :: !Indis;
    NONE )
  else
    let
      val M = max( fn( X, Y ) => synt_compl X < synt_compl Y, !Indis )
    in
      if synt_compl M < synt_compl Indi + Epsilon then
        SOME Indi
      else (
        Indis := Indi :: 
          filter( fn X => not( real_rep_eq( fingerprint X, fingerprint M )), 
                  !Indis );
        SOME M )
    end


fun update_output_class_check(
      find_id : '1a -> Id.id,
      fingerprint : '1a -> real,
      synt_compl : '1a -> real,
      Output_class as ( _, _, Indis ) : '1a output_class,
      Indi : '1a )  : bool =
  let
    val Oc = output_class_clone Output_class
    fun indi_eq(X,Y) = find_id X = find_id Y
  in
    update_output_class( fingerprint, synt_compl, Oc, Indi );
    not( list_eq( indi_eq, !Indis, !(#3 Oc) ) )
  end








fun output_class_indis( ( _, _, Indis ) : '1a output_class ) = !Indis
 

fun output_class_out( 
      fingerprint : '1a -> real,
      synt_compl : '1a -> real,
      out, 
      indi_out : outstream * '1a -> unit,
      ( _, _, Indis ) : '1a output_class ) : unit =
  let
    fun p S = output(out,S);
    fun elem_out Indi = (
      p( "Synt compl = " ^ Real.toString( synt_compl Indi )  ^ "    " );
      p( "Fingerprint = " ^ Real.toString( fingerprint Indi )  ^ "\n");
      indi_out(out,Indi); 
      p"\n\n"
      )
  in
    loop(elem_out,!Indis)
  end

(*

(* Test code: *)

val Xs : ( Id.id * real * real ) output_class = 
  create_output_class( (Id.gen_id(), 1.0, 0.123), 3 )

fun find_id(X,_,_) = X
fun synt_compl(_,Y,_) = Y
fun fingerprint(_,_,Z) = Z

val u = fn (S,F) => 
  let
    val New = ( Id.gen_id(), S, F )
    val Check =
      update_output_class_check( find_id, fingerprint, synt_compl, Xs, New )
  in
    ( Check, update_output_class( fingerprint, synt_compl, Xs, New ) )
  end

val i = fn() => output_class_indis Xs

*)

end (* structure Genealogical_search_lib *)
