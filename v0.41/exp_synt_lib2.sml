(* File: exp_synt_lib2.sml.
   Created 1999-07-06.
   Modified 1999-07-06.
*)

structure Exp_synt_lib2 :
sig
  val analyzed_order_ok : ('a,'b)Ast.e -> bool
(* Only to be used when synting for DUPL. Is applied to the case-exp synted
   so far to avoid equivalence due to analyzing exps in different order.
*)
end =
struct
open Lib List1 Ast Ast_lib

type 'a node = { node_id : int, info : 'a }

fun roots( Nodes : 'a node list, Edges : ( 'a node * 'a node ) list )
    : 'a node list =
let
  val Is_root = Array.array( 1+max( op<, map( #node_id, Nodes ) ), true )
in
  loop( fn( From, To ) => Array.update( Is_root, #node_id To, false ), Edges );
  filter( fn{ node_id, ... } => Array.sub( Is_root, node_id ), Nodes )
end

fun is_lex_top_sorted( less : 'a * 'a -> bool, 
      ( Nodes : 'a node list, Edges : ( 'a node * 'a node ) list ) ) : bool =
  case Nodes of 
    [] => true
  | Node1 :: Nodes1 =>
  let
    val less' = fn( X : 'a node, Y : 'a node ) => less( #info X, #info Y )
    val Min_root = min( less', roots( Nodes, Edges ) )
  in
    #node_id Min_root = #node_id Node1 andalso
    is_lex_top_sorted( less, ( Nodes1, filter( fn( From, To ) =>
      #node_id From <> #node_id Node1 andalso #node_id To <> #node_id Node1,
      Edges ) ) )
  end

fun analyzed_exps_and_pat_vars( case_exp{ exp = E, rules, ... } )
    : ( ('a,'b)e * symbol list ) list =
let
  val Case_rules = filter( fn { exp, ... } => is_case_exp exp, rules )
in
  case Case_rules of
    [] => [ ( E, [] ) ]
  | [ { pat, exp, ... } ] => 
      ( E, vars_in_pat pat ) :: analyzed_exps_and_pat_vars exp
end

structure H = Symbol_HashTable

exception Dependency_dag_exn
fun dependency_dag( E : ('a,'b)e ) 
    : ('a,'b)e node list * ( ('a,'b)e node * ('a,'b)e node ) list =
let
  val Xs = analyzed_exps_and_pat_vars E
  val Xs = indexize( Xs, 0 )
  val T : ('a,'b)e node H.hash_table = H.mkTable( 16, Dependency_dag_exn )
  val () =
    loop( fn( ( E, Vars ), I ) =>
      loop( fn  V => H.insert T ( V, { node_id = I, info = E } ), Vars ),
      Xs )
  val Nodes = map( fn( (E,_), I ) => { node_id = I, info = E }, Xs )

(* If node To uses a var defined by From, there is an edge (From,To). *)
  val Edges =
    flat_map( fn To => 
      flat_map( fn V =>
        if is_variable V then
          case H.find T V of
            NONE => []
          | SOME From => [ ( From, To ) ]
        else
          [],
        zero_arity_apps( #info To ) ),
      Nodes )
  in
    ( Nodes, Edges )
  end

fun exp_less( E1, E2 ) = exp_hash E1 < exp_hash E2
  
fun analyzed_order_ok( E : ('a,'b)e ) : bool =
  case E of
    app_exp{ ... } => true
  | case_exp{...} => is_lex_top_sorted( exp_less, dependency_dag E )



end (* structure Exp_synt_lib2 *)


