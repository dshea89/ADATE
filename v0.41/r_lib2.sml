(* File: r_lib2.sml.
   Created 1998-10-02.
   Modified 1998-10-06.
*)

signature R_lib2_sig =
sig

  val cse : ( 'a, 'b )Ast.d * Ast_lib.pos list ->
            ( 'a, 'b )Ast.d * Ast_lib2.CSE_record list

val make_emittable : 
  Ast_lib2.so_far -> Ast.dec * Ast_lib2.Simple_R_and_CSE_records

end

functor R_lib2_fn( R_lib : R_lib_sig ) : R_lib2_sig =
struct

(* 
cse = common subexpression elimination. 
lcp = longest common prefix.
cco = call count overflow.
*)

structure Exp_synt = R_lib.Exp_synt
structure Evaluate = Exp_synt.Synt_lib.Evaluate

open Lib List1 Ast Ast_lib Ast_lib2 Print Exp_synt.Synt_lib Evaluate R_lib

exception Cse_exn1
exception Cse_exn2

fun lcp( Xs, Ys ) = longest_common_prefix[ Xs, Ys ]

(* Finding allowed cse positions: *)
local

datatype tree = leaf of pos | lcp_node of pos * tree list

(*
local

fun n_blanks N = loop( fn _ => p" ", fromto( 1, N ) )

fun print_tree1( N, Xs : tree ) : unit =
  case Xs of
    leaf Pos => ( n_blanks N; p"leaf "; print_pos Pos; nl() )
  | lcp_node( Pos, Xs ) => (
      n_blanks N;
      p"lcp_node "; print_pos Pos; nl();
      loop( fn X => print_tree1( N+2, X ), Xs )
      )

in

fun print_tree Xs = print_tree1( 0, Xs )

end
*)

fun get_pos( leaf Pos ) = Pos
  | get_pos( lcp_node( Pos, _ ) ) = Pos

fun node_is_prefix( X, Pos ) = is_prefix( get_pos X, Pos )

fun find_prefix( Xs : tree list, Pos : pos ) : ( tree * tree list ) option =
  case pfilter( fn X => node_is_prefix( X, Pos ), Xs ) of
    ( [], _ ) => NONE
  | ( [ X ], Xs ) => SOME( X, Xs )

fun find_new_lcp( Old_lcp : pos, Pos : pos, Xs : tree list )
    : ( tree * tree list ) option =
  case pfilter( fn X => lcp( Pos, get_pos X ) <> Old_lcp, Xs ) of
    ( [], _ ) => NONE
  | ( [ X ], Xs ) => SOME( X, Xs )

fun insert( Pos : pos, T : tree ) : tree =
  case T of
    leaf Pos1 =>
      if prefix_related( Pos, Pos1 ) then 
        raise Cse_exn1
      else
        lcp_node( lcp( Pos, Pos1 ), [ leaf Pos, T ] )

  | lcp_node( Lcp, Xs ) =>
  if is_prefix( Pos, Lcp ) then
    raise Cse_exn2
  else if is_prefix( Lcp, Pos ) then
    case find_prefix( Xs, Pos ) of
      NONE => (
        case find_new_lcp( Lcp, Pos, Xs ) of
          NONE => lcp_node( Lcp, leaf Pos :: Xs )
        | SOME( X, Xs ) =>
            lcp_node( Lcp,
              lcp_node( lcp( Pos, get_pos X ), [ leaf Pos, X ] ) :: 
              Xs )
        )
    | SOME( X, Xs ) => lcp_node( Lcp, insert( Pos, X ) :: Xs )
  else
    lcp_node( lcp( Pos, Lcp ), [ leaf Pos, T ] )

fun leaves( T : tree ) : pos list =
  case T of
    leaf Pos => [ Pos ]
  | lcp_node( _, Xs ) => flat_map( leaves, Xs )

fun choose( T : tree, is_allowed : pos * pos list -> bool ) 
    : ( pos * pos list ) list =
  case T of
    leaf _ => []
  | lcp_node( Lcp, Xs ) =>
  case leaves T of Leaves =>
  if is_allowed( Lcp, Leaves ) then
    [ ( Lcp, Leaves ) ]
  else
    flat_map( fn X => choose( X, is_allowed ), Xs )

in (* local *)

fun choose_cse_poses( Poses : pos list, is_allowed : pos * pos list -> bool )
    : ( pos * pos list ) list =
(* Try possible cse poses in top-down order. *)
let
  fun g [ Pos ] = leaf Pos
    | g( Pos :: Poses ) = insert( Pos, g Poses )
  
  val T = g Poses
in
  choose( T, is_allowed )
end

end (* local *)


exception Apply_cse_exn
fun apply_cse( E : ( 'a, 'b )e, Common_poses as Common_pos :: _ : pos list,
      Lcp : pos ) : ( 'a, 'b )e * ( 'a, 'b )e * ( 'a, 'b )e =
let
  val Common = pos_to_sub( E, Common_pos )
  val Sub = pos_to_sub( E, Lcp )
  val V_exp = gen_var_exp( get_exp_info Common )
  
  fun g [] = Sub
    | g( Pos :: Poses ) = pos_replace( g Poses, Pos, fn _ => V_exp )
  
  val N = length Lcp
  val _ = 
    if forall( fn Pos => take( N, Pos ) = Lcp, Common_poses ) then 
      ()
    else
      raise Apply_cse_exn

  val Sub = g( map( fn Pos => drop( N, Pos ), Common_poses ) )
in
  (
  pos_replace( E, Lcp, fn _ =>
    case_exp{ exp = Common, rules = [ mk_new_rule( V_exp, Sub ) ],
      exp_info = get_exp_info Sub } ),
  V_exp,
  Sub 
  )
end

(*
Determining if a given cse should be allowed
--------------------------------------------

sc = syntactic complexity
Min = Min possible execution count.
Max = Max possible execution count.

Possible cco      Smaller sc        Allowed
------------      ----------        -------
false             false             false
false             true              true
true              false             Min >= 1 andalso Max >= 2
true              true              Min >= 1
*)

fun min_execution_count'( 
      Syms_and_mults : ( symbol * int ) list, 
      E : ( 'a, 'b )e 
      ) : int =
let
  fun mec Sub = min_execution_count'( Syms_and_mults, Sub )
in
  case E of
    app_exp{ func, args, ... } => 
      (
      case assoc_opt( func, Syms_and_mults ) of
        NONE => 0
      | SOME N => N
      ) + int_sum( map( mec, args ) )
  | case_exp{ exp, rules, ... } => 
      let
        val rules = 
          filter( fn { exp, ... } => not( is_not_activated_exp exp ), rules )
      in
        mec exp + 
        ( if null rules then 0 else min( op<, map( mec o #exp, rules ) ) )
      end
  | let_exp{ dec_list, exp, ... } =>
    let
      val Funcs_and_mecs = map( fn{ func, exp, ... } =>
        ( func, mec exp ),
        dec_list )
    in
      min_execution_count'( Funcs_and_mecs @ Syms_and_mults, exp )
    end
end
      
fun min_execution_count( Sym : symbol, E : ( 'a, 'b )e ) : int =
  min_execution_count'( [ ( Sym, 1 ) ], E )



fun max_execution_count'( 
      Syms_and_mults : ( symbol * int ) list, 
      E : ( 'a, 'b )e 
      ) : int =
let
  fun mec Sub = max_execution_count'( Syms_and_mults, Sub )
in
  case E of
    app_exp{ func, args, ... } => 
      (
      case assoc_opt( func, Syms_and_mults ) of
        NONE => 0
      | SOME N => N
      ) + int_sum( map( mec, args ) )
  | case_exp{ exp, rules, ... } => 
      let
        val rules = 
          filter( fn { exp, ... } => not( is_not_activated_exp exp ), rules )
      in
        mec exp + 
        (if null rules then 0 else max( op<, map( mec o #exp, rules ) ) )
      end
  | let_exp{ dec_list, exp, ... } =>
    let
      val Funcs_and_mecs = map( fn{ func, exp, ... } =>
        ( func, mec exp ),
        dec_list )
    in
      max_execution_count'( Funcs_and_mecs @ Syms_and_mults, exp )
    end
end
      
fun max_execution_count( Sym : symbol, E : ( 'a, 'b )e ) : int =
  max_execution_count'( [ ( Sym, 1 ) ], E )





exception Cse_is_allowed_exn

fun cse_is_allowed( 
      D as { exp, ... } : ( 'a, 'b )d,
      Common_poses as Common_pos :: _ : pos list,
      Lcp : pos ) : bool =
  case pos_to_sub( exp, Common_pos ) of Common =>
  common_scope_check( Common, pos_to_sub( exp, Lcp ) ) andalso
  let
    val ( New_exp, V_exp, Sub ) = apply_cse( exp, Common_poses, Lcp )
    val app_exp{ func = V, args=nil, ... } = V_exp
    val New_D = set_exp( D, New_exp )
    val Possible_cco = not( null(
      exp_filter(
        fn app_exp{ func, args = _::_, ... } =>
             not( Predefined.is_constructor func )
         | _ => false,
        Common )
      ) )

    val Empty' : unit Symbol_HashTable.hash_table =
      Symbol_HashTable.mkTable( 0, Cse_is_allowed_exn )

    fun sc D = hd( syntactic_complexities( D, Empty' ) )
    val Smaller_sc = sc New_D < sc D
  in
  case Possible_cco of
    false => Smaller_sc
  | true =>
      min_execution_count( V, Sub ) >= 1 andalso 
      ( Smaller_sc orelse max_execution_count( V, Sub ) >= 2 )
  end (* fun cse_is_allowed *)

exception Cse_exn3

fun cse( D : ( 'a, 'b )d, Common_poses : pos list ) 
    : ( 'a, 'b )d * CSE_record list=
let
  fun is_allowed( Lcp : pos, Common_poses : pos list ) : bool =
    cse_is_allowed( D, Common_poses, Lcp )
  
  val Lcp_poses : ( pos * pos list ) list = 
    choose_cse_poses( Common_poses, is_allowed )

  fun g [] = ( #exp D, [] )
    | g( ( Lcp, Common_poses ) :: Lcps ) =
        case g Lcps of ( E, Records ) =>
          ( #1( apply_cse( E, Common_poses, Lcp ) ),
            { case_pos = Lcp,
              common_poses_before = Common_poses,
              v_poses =
                case length Lcp of N =>
                map( fn Common_pos => 
                  if take( N, Common_pos ) <> Lcp then raise Cse_exn3 else
                  Lcp @ [1] @ drop( N, Common_pos ),
                  Common_poses )
               } :: Records )
in
  case g Lcp_poses of ( E, Records ) =>
  ( set_exp( D, E ), Records )
end

fun make_emittable So_far =
  R_lib.So_far.make_emittable( cse, So_far )

end (* functor R_lib2_fn *)


