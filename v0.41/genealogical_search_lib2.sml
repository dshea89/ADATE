(*
  File: genealogical_search_lib2.sml
  Created: 1999-06-26.
  Modified: 2002-10-01.
*)

structure Genealogical_search_lib2 :
sig
 
type 'a time_class = { 
  time_class_card : int, 
  indis : 'a SplayTree.splay ref,
  time_compl : 'a -> real,
  synt_compl : 'a -> real,
  base : 'a
  }

val create_time_class : int * ( 'a -> real ) * ( 'a -> real ) * 'a ->
      'a time_class

val time_class_indis : 'a time_class -> 'a list
val time_class_base : 'a time_class -> 'a 

val update_time_class : 'a time_class * 'a  -> 'a list

val update_time_class_check : ( 'a -> Id.id ) * 'a time_class * 'a  -> bool

val time_class_out : 
  Lib.outstream * ( Lib.outstream * 'a -> unit ) * 'a time_class -> unit

end =
struct
open Lib List1 Ast Ast_lib Genealogical_search_lib

(* 

Time Complexity Class
---------------------

Let S denote syntactic complexity and T time complexity. A time complexity
class with n elements with values (S1,T1), (S2,T2), ..., (Sn,Tn) is ordered
so that S1<S2<...<Sn and T1>T2>...>Tn. This ordering is maintained as
for base individuals but using time complexity for comparison.
The ordering is maintained using update_bests in genealogical_search_lib.sml.

To avoid having too big Sn through beta-expansion, it is required that 
Sn <= 2( S0 + 50 ) where S0 is the syntactic complexity of the 
base indi that the class is piggy-backed on.

The cardinality n is allowed to vary between Time_class_card and 
2Time_class_card where Time_class_card is a constant defined in 
the specification.

A time class is pruned using a base factor Alpha which is squared when a class
is to be pruned. Let the initial value of Alpha be Alpha' = 0.99999.
The target values for time complexities are T0 * Alpha^i. The squaring
reduces "swing-in" since half of the target values are kept.

Each target picks its favourite time. Only picked times are kept during
pruning. The favourite of a target is either its time lub or its time glb.
*)

exception Alpha_exn
fun alpha( T0 : real, Tn : real, Time_class_card : int ) : real =
let
  val () = 
    if Time_class_card < 1 orelse T0 < 1.0E~100 orelse Tn < 1.0E~100 orelse T0 <= Tn 
       orelse T0 > 1.0E100 orelse Tn > 1.0E100
    then
      raise Alpha_exn
    else 
      ()
            
  open Math
  val Alpha' = 0.99999
  fun log2 X = ln X / ln 2.0
  val K = floor( log2( ln( Tn / T0 ) / ( real Time_class_card * ln Alpha' ) ) )
in
  real_pow( Alpha', real_pow( 2.0, real K ) )
end

structure S = Splay_lib

exception Prune_exn
fun prune( T0 : real, Ts : ( real * 'a ) list, Time_class_card : int ) 
    : { kept : ( real * 'a ) list, knocked_out : ( real * 'a ) list } =
  if Time_class_card <= 0 then
    { kept = [], knocked_out = Ts }
  else if length Ts <= 1 then
    { kept = Ts, knocked_out = [] }
  else (* length Ts >= 2 *)
  let
    val Alpha = alpha( T0, #1( dh Ts ), Time_class_card )

    val Targets = 
      map( fn I => T0 * real_pow( Alpha, real I ), 
        fromto( 1, 3 * Time_class_card + 2 ) ) (* Margin added here. *)

    val Times = S.fromList( map( fn( T, Indi ) => ( T, Indi, false ), Ts ) )

    fun cmp( ( T1, _, _ ), ( T2, _, _ ) ) = real_compare( T2, T1 )

    val () = if S.is_ordered( cmp, Times ) then () else raise Prune_exn
    fun mk_node( Target : real ) : real * 'a * bool = 
      ( Target, #2(hd Ts), false ) (* #2(hd Ts) and false are dummy values. *)
 
    fun g( Targets, Times ) =
      case Targets of
        [] => Times
      | Target :: Targets =>
      let
        val Target_node = mk_node Target
        val ( ( T, Indi, Chosen ), Times ) =
          case S.lub( cmp, Target_node, Times ) of ( Opt, Times ) =>
          case Opt of
            NONE => ( 
              case S.glb( cmp, Target_node, Times ) of 
                ( SOME X, Times ) => ( X, Times ) )
         | SOME( X as ( Tlub : real, _, _ ) ) =>
         case S.glb( cmp, Target_node, Times ) of ( Opt, Times ) =>
         case Opt of
           NONE => ( X, Times )
         | SOME( Y as ( Tglb : real, _, _ ) ) =>
             if abs( Tlub - Target ) < abs( Tglb - Target ) then
               ( X, Times )
             else
               ( Y, Times )
      in
        g( Targets,
          if Chosen then
            Times
          else
            S.insert( cmp, ( T, Indi, true ), 
              S.delete( cmp, ( T, Indi, Chosen ), Times ) ) )
      end

    val Times = g( Targets, Times )
    val ( Kept, Knocked_out ) = 
      pfilter( fn( _, _, Chosen ) => Chosen, S.inorder Times )
  in
    { kept = map( fn( T, Indi, _ ) => ( T, Indi ), Kept ),
      knocked_out = map( fn( T, Indi, _ ) => ( T, Indi ), Knocked_out ) }
  end (* fun prune *)

        

type 'a time_class = { 
  time_class_card : int, 
  indis : 'a SplayTree.splay ref,
  time_compl : 'a -> real,
  synt_compl : 'a -> real,
  base : 'a
  }

fun time_class_base( { base, ... } : 'a time_class ) = base

fun coarsify Rel =  Real.realCeil( 100.0 * Rel ) 

fun create_time_class( Time_class_card, time_compl, synt_compl, Base)
    : 'a time_class = 
let
  val T0 = time_compl Base
  fun time_compl'( X : 'a ) =
    case time_compl X of T => ( 
(*
      p"\nT0 = "; print_real T0;
      p" T = "; print_real T;
      p" coarse = "; print_real(coarsify( T / T0 ) + 1.0e~20 );
*)
      coarsify( T / T0 ) + 1.0e~20 
      )
in {
  time_class_card = Time_class_card, indis = ref SplayTree.SplayNil, time_compl = time_compl', 
  synt_compl = synt_compl, base = Base }
end

fun time_class_clone{ time_class_card, indis, time_compl, synt_compl, base } = {
  time_class_card = time_class_card, indis = ref( !indis ), time_compl = time_compl,
  synt_compl = synt_compl, base = base }


fun update_time_class( Time_class : 'a time_class, New : 'a ) : 'a list =
let
  val { time_class_card, indis, time_compl, synt_compl, base } = Time_class
  fun time_cmp( X : 'a, Y : 'a ) = real_compare( time_compl X, time_compl Y )
  fun synt_compl_cmp( X : 'a, Y : 'a ) = 
    real_compare( synt_compl X, synt_compl Y )
in
  if  time_compl New >= time_compl base orelse
     synt_compl New > 2.0 * ( 50.0 + synt_compl base )
  then
    [ New ]
  else
let
  val ( Knocked_out, Indis ) =
     update_bests( time_cmp, synt_compl_cmp, fn X => X, New, !indis )
    
  val { kept, knocked_out } = 
    prune( 
       time_compl base, 
       map( fn Indi => ( time_compl Indi, Indi ), rev( S.inorder Indis ) ),
       time_class_card )
in
  indis := S.fromList( map( #2, rev kept ) );
  map( #2, knocked_out ) @ Knocked_out
end
end
  
fun time_class_indis( Time_class : 'a time_class ) : 'a list =
  S.inorder( !( #indis Time_class ) )
  

fun update_time_class_check( 
      find_id : 'a -> Id.id, 
      Time_class : 'a time_class,
      New : 'a ) : bool =
  let
    val Time_class_copy = time_class_clone Time_class
    fun indi_eq(X,Y) = find_id X = find_id Y
  in
    update_time_class( Time_class_copy, New );
    not( list_eq( indi_eq, time_class_indis Time_class_copy, time_class_indis Time_class ) )
  end


fun time_class_out( 
      out, 
      indi_out : outstream * 'a -> unit,
      { indis, ... } : 'a time_class ) : unit =
  let
    fun p S = output(out,S);
    fun elem_out Indi = (
      p"\n";
      indi_out(out,Indi); 
      p"\n"
      )
  in
    loop(elem_out, rev( S.inorder( !indis ) ) )
  end


end (* structure Genealogical_search_lib2 *)

















