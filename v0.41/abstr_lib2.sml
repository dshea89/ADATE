(* File: abstr_lib2.sml.
   Created: 1999-08-10.
   Modified: 1999-08-10.
*)


functor Abstr_lib2_fn( Synt_lib : SYNT_LIB ) : 
sig

val mk_case_exps_and_subst : 
  Ast.exp * Ast.exp * Ast.exp_info_type -> (Ast.exp -> Ast.exp) * 
    ( Ast.exp_info_type, Ast.dec_info_type )Ast_lib.exp_subst

end =
struct
open Lib List1 Ast Ast_lib Ast_lib2

(*

Constructor-Substitutive Abstraction
------------------------------------

Assume that Ei in the pre-body H( ..., Ei, ... ) is
cons( point(X1,Y1), cons(P2,Xs1) ) and that the new parameter Zs is
to replace Ei. The following case-expression is inserted at the top of the body:

case Zs of
  nil => ?_NA1
| cons( Q1 as point(Q1x,Q1y), Zs1 ) =>
case Zs1 of
  nil => ?_NA2
| cons( Q2 as point(Q2x,Q2y), Zs2 ) => Body

The following substitution is applied to the body:

{ point(X1,Y1) -> Q1, X1 -> Q1x, Y1 -> Q1y, cons(P2,Xs1) -> Zs1,
  P2 -> Q2, Xs1 -> Zs2 }

*)

type exp_subst = ( exp_info_type, dec_info_type )exp_subst

fun compose_transforms [] = (fn X => X)
  | compose_transforms( t :: ts ) = (fn X => t( compose_transforms ts X ))

fun contains_variable E = not( null( exp_filter( is_variable_exp, E ) ) )
     
fun mk_case_exps( Ei : exp, Vi :  exp, Body_type : exp_info_type ) 
    : exp -> exp =
(* The returned function inserts case-exps at the top of its argument which
   should be the body
*)
  if not( contains_variable Ei ) then fn X => X else
  case Ei of
    app_exp{ func, args, exp_info } =>
      if not( Predefined.is_constructor func ) then
        fn X => X
      else
      let
        val case_exp{ exp, rules, ... } =
          Synt_lib.construct_case_exp( Body_type, Vi )

        val rules = map( fn{ pat, exp, ... } =>
          mk_new_rule( pat, gen_not_activated_exp Body_type ),
          rules )

        val Case_exp = 
          case_exp{ exp = exp, rules = rules, exp_info = Body_type }

        val [ ( { pat, ... }, No ) ] =
          filter( fn( { pat = app_exp{ func = F, ... }, ... }, _ ) => F = func
                  | ( _, _ ) => false,
            indexize( rules, 1 ) )

        val t = mk_case_exps'( Ei, pat, Body_type )
      in
        fn Body => pos_replace( Case_exp, [No], fn _ => t Body )
      end
  | _ => fn X => X

and mk_case_exps'( E, Pat, Body_type ) =
  case Pat of
    as_exp{ pat, ... } => mk_case_exps'( E, pat, Body_type )
  | app_exp{ func = F, args = Pat_args, ... } =>
  if null Pat_args then
    if is_variable F then
      mk_case_exps( E, Pat, Body_type )
    else
      fn X => X
  else
    case E of
      app_exp{ func, args, ... } => (
        if func = F then
          compose_transforms( map( fn( E, Pat ) => 
            mk_case_exps'( E, Pat,  Body_type ),
            combine( args, Pat_args ) ) )
        else
          fn X => X )
    | _ => fn X => X

fun mk_pat_subst( E, 
                  Pat as app_exp{ func = F, args = Pat_args, ... } 
                  ) : exp_subst =
      if null Pat_args then
        if is_variable F then
          if contains_variable E then [ ( E, Pat ) ] else []
        else
          []
      else (
      case E of
        app_exp{ func, args, ... } =>
          if func <> F then
             []
           else
             flat_map( mk_pat_subst, combine( args, Pat_args ) )
      | _ => [] )

  | mk_pat_subst( E, as_exp{ var, pat, exp_info } ) =
      if not( contains_variable E ) then
        []
      else
        ( E, app_exp{ func = var, args=[], exp_info = exp_info } ) ::
        mk_pat_subst( E, pat )
                  
  
fun mk_subst( E, Case_exp ) : exp_subst =
  case ( E, Case_exp ) of
    ( app_exp{ func, args, ... }, case_exp{ rules, ... } ) =>
    if not( Predefined.is_constructor func ) then [] else
    let
      val [ ( { pat, ... }, No ) ] =
        filter( fn( { pat = app_exp{ func = F, ... }, ... }, _ ) => F = func
                | ( _, _ ) => false,
          indexize( rules, 1 ) )

      val Pat_subst = mk_pat_subst( E, pat )
    in
      Pat_subst @ 
      flat_map( fn( E, Desired_analyzed ) => 
        mk_subst'( E, Case_exp, Desired_analyzed ),
        Pat_subst )
    end
  | ( _, _ ) => []

and mk_subst'( E, Case_exp, Desired_analyzed ) =
  case Case_exp of
    case_exp{ exp, rules, ... } =>
      if exp_eq( exp, Desired_analyzed ) then
        mk_subst( E, Case_exp )
      else
        flat_map( fn{ exp, ... } => mk_subst'( E, exp, Desired_analyzed ),
                  rules )
  | _ => []

fun mk_case_exps_and_subst( Ei, Vi, Body_type ) : (exp -> exp) * exp_subst =
let
  val t : exp -> exp = mk_case_exps( Ei, Vi, Body_type )
in
  ( t, mk_subst( Ei, t( dummy_exp Body_type ) ) )
end

end (* functor Abstr_lib2_fn *)
