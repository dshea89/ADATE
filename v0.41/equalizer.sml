(*
File: equalizer.sml
Created: 2002-11-09
Modified: 2002-11-13

The following code is used to choose the next parent, attempting to 
uniformly distribute CPU time on syntactic complexity.

Candidates is a list of programs from which a parent is to be chosen.

Consumption is a dynamic array, indexed by complexity, giving the total time 
spent on expanding programs of a given complexity.
*)
structure Equalizer :
sig
      
val chooseParent :
      ( 'a -> real ) *
      ( 'a -> real ) *
      'a list ->
      'a * real

val printConsumption : unit -> unit
val updateConsumption : real * real -> unit
val getConsumption : unit -> real list
val setConsumption : real list -> unit

end =
struct
open Lib List1 Ast Ast_lib Genealogical_search_lib

fun toIndex( Compl : real ) : int = 
  case Compl >= 0.0 of true => floor( Compl / 100.0 )

(* After executing the following function, it only remains to select a parent
based on max_cost_limit_used.
*)
fun candidateParents(
      Indis : 'a list Array.array,
      Consumption : real Array.array
      ) : 'a list =
let
  val Indis = array_to_list Indis
  val Consumption = array_to_list Consumption
  val true = length Indis = length Consumption
  val Xs = zip( Indis, Consumption )
  fun less( (_,C1), (_,C2) ) = C1 < C2
  val Xs = sort less Xs
  val ( Cands, _ ) ::_ = dropwhile( fn( Cands, _ ) => null Cands, Xs )
in 
  Cands
end
 
      
fun chooseParent'(
      getComplexity : 'a -> real,
      max_cost_limit_used : 'a -> real,
      Candidates : 'a list,
      Consumption : Real_dyn.array
      ) : 'a =
let
  val MaxIndex = max( op<, map( toIndex o getComplexity, Candidates ) )
  (* val () = (p"\nMaxIndex = "; print_int MaxIndex; nl() ) *)
  val N = MaxIndex+1
  val Consumption : real Array.array =
    Array.tabulate( N, fn I => Real_dyn.sub( Consumption, I ) )
  val Indis : 'a list Array.array = Array.array( N, [] )
  val () = loop( fn Indi =>
    case toIndex( getComplexity Indi ) of I =>
    case Array.sub( Indis, I ) of Xs =>
      Array.update( Indis, I, Indi :: Xs ),
    Candidates )
  val Cands = candidateParents( Indis, Consumption )
  fun less( X, Y ) = 
    case Real.compare( max_cost_limit_used X, max_cost_limit_used Y ) of
      LESS => true
    | GREATER => false
    | EQUAL => getComplexity X < getComplexity Y
in
  min( less, Cands )
end

val Consumption = Real_dyn.array( 1, 0.0 )

fun printConsumption() =
  loop( fn I => 
    ( p" "; print_int I; p": "; print_real( Real_dyn.sub( Consumption, I ) ) ),
    fromto( 0, Real_dyn.bound Consumption ) )
    


fun updateConsumption( Complexity : real, ExpansionTime : real ) : unit =
let
  val I = toIndex Complexity
  val X = Real_dyn.sub( Consumption, I )
in
  Real_dyn.update( Consumption, I, X + ExpansionTime )
end

fun getConsumption() =
  map( fn I => Real_dyn.sub( Consumption, I ), 
    fromto( 0, Real_dyn.bound Consumption ) )

fun setConsumption( To : real list ) : unit =
let
  val To = rev( dropwhile( fn C => C <= 0.0, rev To ) )
  val To = Array.fromList To
  val N = Array.length To
in
  Real_dyn.truncate( Consumption, N );
  for( 0, N-1, fn I => 
    Real_dyn.update( Consumption, I, Array.sub( To, I ) ) )
end

      
fun chooseParent(
      getComplexity : 'a -> real,
      max_cost_limit_used : 'a -> real,
      Candidates : 'a list
      ) : 'a * real = 
case
  chooseParent'( getComplexity, max_cost_limit_used, Candidates, Consumption )
of
  Parent => ( Parent, 
  max2( op<, 
    Constants.Initial_cost_limit, 
    Constants.Alpha * max_cost_limit_used Parent ) )
    
end (* structure Equalizer *)
