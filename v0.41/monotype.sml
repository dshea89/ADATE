(*
File: monotype.sml.
Created: 1999-02-16.

Quick monomorphic type checking.
*)


functor Mono_type_fn( Evaluate : EVALUATE ) :
sig
  val type_check_dec_raise : Ast.dec -> unit
end =
struct

open Lib List1 Ast Ast_lib Print


datatype mono_ty =
  leaf of symbol
| funty of symbol list * symbol

fun ty_sym_of_ty_exp( ty_con_exp( Ty_sym, [] ) ) = Ty_sym

fun ty_sym_of_exp( E : exp ) : symbol = ty_sym_of_ty_exp( type_of_exp E )

fun range_ty_sym( Type : ty_exp ) = ty_sym_of_ty_exp( range_type Type )

fun domain_ty_syms( Type : ty_exp ) : symbol list =
  map( ty_sym_of_ty_exp, domain_type Type )

fun pat_comps( Pat : exp ) : ( symbol * symbol )list =
  map( fn( Sym, { schematic_vars=[], ty_exp } ) =>
    ( Sym, ty_sym_of_ty_exp ty_exp ),
    comps_in_pat Pat )

fun mk_funty( Type : ty_exp ) : mono_ty =
  funty( domain_ty_syms Type, range_ty_sym Type )

fun ty_env_to_mono_ty_env( Ty_env : ty_env ) : ( symbol * mono_ty ) list =
  map( fn( Sym, { schematic_vars=[], 
                  ty_exp = ty_exp as ty_con_exp( Ty_con, _ ) } ) =>
    ( Sym, 
      if Ty_con = THIN_ARROW then
        mk_funty ty_exp
      else
        leaf( ty_sym_of_ty_exp ty_exp ) ),
    Ty_env )

structure H = Symbol_HashTable

exception Type_check_dec_exn
fun type_check_dec( D : dec ) =
let
  val T : mono_ty H.hash_table = H.mkTable( 100, Type_check_dec_exn )

  fun peek Sym = H.find T Sym

  fun lookup Sym = H.lookup T Sym
    handle Ex => (
      p( "\nlookup: symbol " ^ symbol_to_string Sym ^ " not found." );
      re_raise( Ex, "lookup" ) )

  fun ins( Sym, Ty ) = 
    ( case peek Sym of NONE => H.insert T ( Sym, Ty ) )
    handle Ex => (
      p( "\nins: symbol " ^ symbol_to_string Sym ^ " could not be inserted!" );
      re_raise( Ex, "ins" ) )

  fun del Sym = H.remove T Sym

  val () = loop( ins, ty_env_to_mono_ty_env( Predefined.ty_env() ) )
  
  exception Tc_exp_not_implemented_exn

  fun tc_dec( D : dec ) : bool =
  let
    val { func, pat, exp, dec_info = { schematic_vars = [], ty_exp } } = D
   
    val Funty as funty( Domain', Range ) = mk_funty ty_exp
(*
    val () = (
      p"\nDomain' = "; print_syms Domain';
      p"tuple_ty_syms returns = ";
      print_syms( tuple_ty_syms( type_of_exp pat ) );
      nl() )
*)
  in
    Domain' = tuple_ty_syms( type_of_exp pat ) andalso
    Range = range_ty_sym( type_of_exp exp ) andalso
  let
    val Pat_comps = pat_comps pat
    val () = loop( fn( S, Ty ) => ins( S, leaf Ty ), Pat_comps )
  in
    tc_pat pat andalso
  let
    val () = ins( func, Funty )
  in
    tc_exp exp andalso (
    del func;
    loop( fn( S, _ ) => del S, Pat_comps );
    true ) 
  end 
  end
  end

  and tc_exp( E : exp ) : bool =
  case E of
    app_exp{ func, args, exp_info } =>
      if func = TUPLE then
        raise Tc_exp_not_implemented_exn
      else if func = SEMICOLON then
      let
        val [ E1, E2 ] = args
        val T = get_ty_exp exp_info
      in
        T = type_of_exp E1 andalso
        T = type_of_exp E2 andalso
        tc_exp E1 andalso tc_exp E2
      end
      else if null args then
        is_q func orelse is_int func andalso
                         ty_sym_of_ty_exp( get_ty_exp exp_info ) = INT orelse
        is_real func andalso ty_sym_of_ty_exp( get_ty_exp exp_info ) = REAL
        orelse
        let
          val leaf Ty = lookup func
        in
          Ty = ty_sym_of_ty_exp( get_ty_exp exp_info )
        end
      else
      let
        val funty( Domain', Range ) = lookup func
      in
        Range = ty_sym_of_ty_exp( get_ty_exp exp_info ) andalso
        length args = length Domain' andalso
        forall( fn( T, Arg ) => T = ty_sym_of_exp Arg, 
                combine( Domain', args ) ) andalso
        forall( tc_exp, args )
      end

  | case_exp{ exp, rules, exp_info } =>
  tc_exp exp andalso
  let
    val T = type_of_exp exp
  in
    forall( fn{ pat, exp, ... } =>
      T = type_of_exp pat andalso 
      type_of_exp exp = get_ty_exp exp_info andalso
      let
        val Pat_comps = pat_comps pat
        val () = loop( fn( S, Ty ) => ins( S, leaf Ty ), Pat_comps )
      in
        tc_pat pat andalso
        tc_exp exp andalso (
        loop( fn( S, _ ) => del S, Pat_comps );
        true )
      end,
      rules )
  end
  
  | let_exp{ dec_list, exp, exp_info } =>
      forall( fn { func, pat, exp, 
                   dec_info = { schematic_vars = [], ty_exp } } =>
      let
        val Funty as funty( Domain', Range ) = mk_funty ty_exp
      in
        Domain' = tuple_ty_syms( type_of_exp pat ) andalso
        Range = range_ty_sym( type_of_exp exp ) andalso
      let
        val Pat_comps = pat_comps pat
        val () = loop( fn( S, Ty ) => ins( S, leaf Ty ), Pat_comps )
      in
        tc_pat pat andalso (
        ins( func, Funty );
        tc_exp exp  ) andalso (
        loop( fn( S, _ ) => del S, Pat_comps );
        true )
      end
      end,
      dec_list ) andalso
      tc_exp exp andalso
      type_of_exp exp = get_ty_exp exp_info andalso (
      loop( fn{ func, ... } => del func, dec_list );
      true )

  and tc_pat( E : exp ) : bool = (
    (* p("\ntc_pat : " ); print_exp E; *) (
  case E of
    app_exp{ func, args, exp_info } =>
      if null args then
        true
      else if func = TUPLE then
        forall( tc_pat, args )
      else  
      let
        val funty( Domain', Range ) = lookup func
        (* val () = p("\nfunc = " ^ symbol_to_string func ) *)
      in
        Range = ty_sym_of_ty_exp( get_ty_exp exp_info ) andalso
        length args = length Domain' andalso
        forall( fn( T, Arg ) => T = ty_sym_of_exp Arg, 
                combine( Domain', args ) ) andalso
        forall( tc_pat, args )
      end 

  | as_exp{ var, pat, exp_info } =>
      type_of_exp pat = get_ty_exp exp_info andalso
      tc_pat pat ) )


in
  tc_dec D
end (* fun type_check_dec *)



exception Type_check_dec_raise_exn
fun type_check_dec_raise( D : dec ) =
(
  if type_check_dec D then () else (
    p"\n\ntype_check_dec_raise:\n";
    print_dec' D;
    print_dec D;
    raise Type_check_dec_raise_exn )
) handle Ex => (
    p"\n\ntype_check_dec_raise:\n";
    print_dec' D;
    print_dec D;
    re_raise( Ex, "type_check_dec_raise" ) )
    




end (* functor Mono_type_fn *)
