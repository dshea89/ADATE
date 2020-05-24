(* File: ast_lib3.sml.
   Created: 1999-08-02.
   Modified: 1999-08-02.
*)



functor hash_table_reverse_functor( H : MONO_HASH_TABLE ) :
sig

val reverse_table : 
  H.Key.hash_key H.hash_table -> H.Key.hash_key list H.hash_table

end =
struct

type item = H.Key.hash_key

exception Reverse_table_exn

fun reverse_table( T : item H.hash_table ) : item list H.hash_table =
let
  val U : item list H.hash_table = 
    H.mkTable( H.numItems T, Reverse_table_exn )

  fun ins( X, Y ) =
    case H.find U X of
      NONE => H.insert U ( X, [Y] )
    | SOME Ys => H.insert U ( X, Y::Ys )
in
  H.appi (fn(Y,X) => ins(X,Y)) T;
  U
end

end (* hash_table_reverse_functor *)


structure Ast_lib3_tmp1 = hash_table_reverse_functor( Lib.Int_HashTable )
structure Ast_lib3_tmp2 = hash_table_reverse_functor( Ast_lib.Symbol_HashTable )

structure Ast_lib3 : 
sig

val syms_and_mults : ( 'a, 'b )Ast.e -> int Ast_lib.Symbol_HashTable.hash_table
val reversible_rename : ('a,'b)Ast.e -> ('a,'b)Ast.e * Ast_lib.sym_subst

val int_hash_table_reverse : 
  int Lib.Int_HashTable.hash_table -> int list Lib.Int_HashTable.hash_table

val symbol_hash_table_reverse : 
  Ast.symbol Ast.Symbol_HashTable.hash_table -> 
  Ast.symbol list Ast.Symbol_HashTable.hash_table

val wrap : Ast.dec -> Ast.dec
val unwrap : Ast.dec -> Ast.dec

end =
struct
open Lib List1 Ast Ast_lib 


structure H = Symbol_HashTable

exception Syms_and_mults_exn
fun syms_and_mults( E : ( 'a, 'b )e ) : int H.hash_table =
let
  val Syms_and_mults = H.mkTable( 100, Syms_and_mults_exn )
  fun ins Sym = 
    case H.find Syms_and_mults Sym of
      NONE => H.insert Syms_and_mults ( Sym, 1 )
    | SOME N => H.insert Syms_and_mults ( Sym, N+1 )

  fun s( app_exp{ func, args, ... } ) = ( ins func; loop( s, args ) )
    | s( case_exp{ exp, rules, ... } ) = ( 
        s exp;
        loop( fn { exp, ... } => s exp, rules )
        )
    | s( let_exp{ dec_list, exp, ... } ) = (
        s exp;
        loop( fn { exp, ... } => s exp, dec_list )
        )
in
  s E;
  Syms_and_mults
end
    
local

exception Reversible_rename_exn

in

fun reversible_rename( E :('a,'b)e ) : ('a,'b)e * sym_subst =
let
  val Renamed_E = rename( E, false )
  val T : sym_subst = H.mkTable( 100, Reversible_rename_exn )

  fun ins( Sym1, Sym2 ) = if Sym1 = Sym2 then () else H.insert T ( Sym1, Sym2 )
 
  fun g( app_exp{ func, args, ... },
          app_exp{ func = F, args = Args, ... } ) = (
            ins( func, F );
            loop( g, combine( args, Args ) )
            )
    | g( case_exp{ exp, rules, ... },
         case_exp{ exp = E, rules = Rules, ... } ) = (
           g( exp, E );
           loop( fn( { pat, exp, ... }, { pat = Pat, exp = E, ... } ) => (
             g( pat, Pat );
             g( exp, E )
             ),
             combine( rules, Rules ) )
           )
    | g( as_exp{ var, pat, ... }, as_exp{ var = V, pat = Pat, ... } ) = (
        ins( var, V );
        g( pat, Pat )
        )
    | g( let_exp{ dec_list, exp, ... },
         let_exp{ dec_list = Ds, exp = E, ... } ) = (
           loop( g_dec,  combine( dec_list,  Ds ) );
           g( exp, E )
           )

  and g_dec( { func, pat, exp, ... }, 
             { func = F, pat = Pat, exp = E, ... } ) = (
        ins( func, F );
        g( pat, Pat );
        g( exp, E )
        )
in
  g( Renamed_E, E );
  ( Renamed_E, T )
end

end (* local *)

val int_hash_table_reverse = Ast_lib3_tmp1.reverse_table

val symbol_hash_table_reverse = Ast_lib3_tmp2.reverse_table






fun to_be_wrapped( { func, exp, ... } : dec ) : bool =
  sym_exp_member( func, exp )
(*
  Two reasons to wrap:

  1. Domain embedding of f. Can be done through ABSTR if there are no recursive
     calls to f.

  2. Post-optimization. Also possible without wrapping if there are no recursive
     calls.
  
  Conclusion: Wrap only if f is called recursively.
*)

fun wrap( { func, pat, exp, dec_info } : dec ) : dec =
  let
    val Renaming = 
      map( fn Var_exp => ( Var_exp, gen_var_exp(type_of_exp Var_exp) ),
           var_exps_in_pat pat )

    val G = gen_func_sym()

    val exp = exp_map(
      fn E as app_exp{ func = F, args, exp_info } =>
           if func = F then
             app_exp{ func = G, args = args, exp_info = exp_info }
           else
             E
       | E => E,
      exp )

    val D : dec = {
      func = G,
      pat = apply_exp_subst( pat, Renaming ),
      exp = apply_exp_subst( exp, Renaming ),
      dec_info = dec_info }

    val Args =
      case pat of
        as_exp{ ... } => [ remove_as pat ]
      | app_exp{ func, args, ... } =>
          if func = TUPLE then
            map( remove_as, args )
          else
            [ remove_as pat ]
  in {
    func = func,
    pat = pat,
    exp = let_exp{
      dec_list = [ D ],
      exp = app_exp{ func = G, args = Args, exp_info = get_exp_info exp },
      exp_info = get_exp_info exp },
    dec_info = dec_info
    }
  end (* fun wrap *)

val wrap = fn D => 
  if to_be_wrapped D then
    let
      (* val () = ( p"\nBefore wrapping:\n"; print_dec' D ) *)
      val D = wrap D
      (* val () = Synt_lib.type_check_dec_raise D *)
      (* val () = ( p"\nAfter wrapping:\n"; print_dec' D ) *)
    in
      D
    end
  else
    D


local

structure H = Symbol_HashTable
exception Unwrap_exn
fun unwrap'( Mults : int H.hash_table,
      D as { func, pat, exp, dec_info } : dec ) : dec =
  case exp of
    let_exp{ dec_list = [ D' ], 
             exp = In_exp as app_exp{ func = G, args, ... }, 
             ... } =>
      if #func D' <> G then D else
      let
        val Args =
          case pat of
            as_exp{ ... } => [ remove_as pat ]
          | app_exp{ func, args, ... } =>
              if func = TUPLE then
                map( remove_as, args )
              else
                [ remove_as pat ]
        val Args' =
          case #pat D' of
            as_exp{ ... } => [ remove_as( #pat D' ) ]
          | app_exp{ func, args, ... } =>
              if func = TUPLE then
                map( remove_as, args )
              else
                [ remove_as( #pat D' ) ]
        val In_exp_mults = syms_and_mults In_exp
      in
        if not( exp_list_eq( args, Args ) ) orelse
           exists( fn V => 
             case H.find Mults V of NONE => false | SOME N1 =>
             case H.find In_exp_mults V of NONE => true | SOME N2 =>
               if N1 < N2 then raise Unwrap_exn else N1>N2, 
             vars_in_pat( #pat D ) )
        then
          D
        else
        let
          val T = H.mkTable( 16, Unwrap_exn )
          val () = H.insert T ( #func D', func )
          val () = loop( fn X => H.insert T X,
            combine( flat_map( vars_in_pat, Args' ), 
                     flat_map( vars_in_pat, Args ) ) )
        in
          apply_sym_subst( D', T )
        end
      end
  | _ => D

in (* local *)

fun unwrap( { func, pat, exp, dec_info } : dec ) : dec =
let
  val Mults = syms_and_mults exp
in
  unwrap'( Mults, { func = func, pat = pat, exp =
    exp_map(
      fn let_exp{ dec_list, exp, exp_info } =>
           let_exp{ dec_list = map( fn D => unwrap'( Mults, D ), dec_list ), 
             exp = exp,
             exp_info = exp_info }
       | E => E,
      exp ),
    dec_info = dec_info } )
end

end (* local *)



(*
val unwrap = fn D => 
  let
    val () = ( p"\nBefore unwrapping:\n"; print_dec' D ) 
    val D = unwrap D
    val () = type_check_dec_raise D
    val () = ( p"\nAfter unwrapping:\n"; print_dec' D )
  in
    D
  end
*)






end (* structure Ast_lib3 *)
