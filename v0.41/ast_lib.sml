(* File: ast_lib.sml.
   Created: 1993-04-??.
   Modified: 1998-12-07.
*)


structure Ast_lib =
struct

open Tree
open List1
open Ast_lib5 Ast

val Max_no_of_cases = 2


fun is_unboxed( { ty_con, ty_pars, alts } : datatype_dec ) : bool =
  forall( fn{constr,domain} => is_NONE domain, alts )

structure Symbol_set = HashSet( Symbol_hash_key )



fun range_type( Type : ty_exp ) : ty_exp =
  case Type of 
    ty_con_exp(Ty_con, _::Range::nil) => 
      if Ty_con = THIN_ARROW then
        Range
      else
        Type
  | _ => Type


fun domain_type( Type : ty_exp ) : ty_exp list =
  case Type of 
    ty_con_exp(Ty_con, Args) => 
      if Ty_con = THIN_ARROW then
        case Args of Domain_type::_::nil => 
        case Domain_type of
          ty_con_exp( Ty_con, Args ) =>
            if Ty_con = TUPLE_TY_CON then
              Args
            else
              Domain_type::nil
        | _ => Domain_type::nil
      else
        []
  | _ => []



local

structure H = Symbol_HashTable 
exception Symbol_intersection

in

fun symbol_intersection( Xs : symbol list, Ys : symbol list ) =
  let
    val Table : unit H.hash_table = 
      H.mkTable( length Xs, Symbol_intersection )
    val _ = loop( fn X => H.insert Table (X,()), Xs )
  in
    filter( fn Y =>
      case H.find Table Y of
        NONE => false
      | SOME _ => true,
      Ys )
  end

end (* local *)



fun root_sym( app_exp{func,...} ) = func
  | root_sym( as_exp{var,...} ) = var

fun symbols_in_app_exp( app_exp{func,args,...} ) =
  func::flat_map(symbols_in_app_exp,args)

exception Tuple_ty_syms
fun tuple_ty_syms( ty_con_exp( Ty_con, [] ) ) = [Ty_con]
  | tuple_ty_syms( ty_con_exp( Ty_con, Args ) ) =
      if Ty_con <> TUPLE_TY_CON then
        raise Tuple_ty_syms
      else
        flat_map( tuple_ty_syms, Args )

fun comps_in_pat( P : exp ) : ty_env =
  case P of
    app_exp{func,args=nil,exp_info} =>
      if is_variable func then
        ( func, {schematic_vars=nil,ty_exp=get_ty_exp exp_info} ) :: nil
      else
        nil
  | app_exp{args,...} => flat_map(comps_in_pat,args)
  | as_exp{var,pat,exp_info} =>
      ( var, {schematic_vars=nil,ty_exp=get_ty_exp exp_info}) :: 
      comps_in_pat pat


fun zero_arity_apps( E : ('a,'b)e ) : symbol list =
  case E of      
    app_exp{func,args=nil,...} => func::nil
  | app_exp{func,args,...} => flat_map(zero_arity_apps,args)
  | let_exp{dec_list,exp,...} =>
      flat_map( fn{exp,...} => zero_arity_apps(exp), dec_list) @ 
      zero_arity_apps(exp)
  | case_exp{exp,rules,...} =>
      zero_arity_apps(exp) @
      flat_map( fn{exp,...} => zero_arity_apps(exp), rules )

fun exp_to_sym( app_exp{func,args=nil,...} ) = func
fun exp_eq( E1 : ('a,'b)e,  E2 : ('c,'d)e ) : bool =
  case E1 of
    app_exp{func,args,...} => (
      case E2 of app_exp{func=func2,args=args2,...} =>
        func=func2 andalso exp_list_eq(args,args2)
      | _ => false
      )
  | case_exp{exp,rules,...} => (
      case E2 of case_exp{exp=exp2,rules=rules2,...} =>
        exp_eq(exp,exp2) andalso 
        exp_list_eq(map(#exp,rules),map(#exp,rules2)) andalso
        exp_list_eq(map(#pat,rules),map(#pat,rules2))
      | _ => false
      )
  | let_exp{dec_list,exp,...} => (
      case E2 of let_exp{dec_list=dec_list2,exp=exp2,...} =>
        exp_eq(exp,exp2) andalso length dec_list=length dec_list2 andalso
        forall(dec_eq,combine(dec_list,dec_list2))
      | _ => false
      )
  | as_exp{var,pat,...} => (
      case E2 of as_exp{var=var2,pat=pat2,...} =>
        var=var2 andalso exp_eq(pat,pat2)
      | _ => false
      )

and dec_eq( {func,pat,exp,...} : ('a,'b)d, 
      {func=func2,pat=pat2,exp=exp2,...} : ('c,'d)d ) :  bool =
  func=func2 andalso exp_eq(pat,pat2) andalso exp_eq(exp,exp2)

and exp_list_eq([],[]) = true
  | exp_list_eq(_,[]) = false
  | exp_list_eq([],_) = false
  | exp_list_eq(E1::Es1,E2::Es2) = exp_eq(E1,E2) andalso exp_list_eq(Es1,Es2)



fun info_exp_eq( E1 : (''a,''b)e,  E2 : (''a,''b)e ) : bool =
  case E1 of
    app_exp{func,args,exp_info} => (
      case E2 of app_exp{func=func2,args=args2,exp_info=exp_info2} =>
        func=func2 andalso exp_info=exp_info2 andalso 
        info_exp_list_eq(args,args2)
      | _ => false
      )
  | case_exp{exp,rules,exp_info} => (
      case E2 of case_exp{exp=exp2,rules=rules2,exp_info=exp_info2} =>
        exp_info=exp_info2 andalso info_exp_eq(exp,exp2) andalso 
        info_exp_list_eq(map(#exp,rules),map(#exp,rules2)) andalso
        info_exp_list_eq(map(#pat,rules),map(#pat,rules2))
      | _ => false
      )
  | let_exp{dec_list,exp,exp_info} => (
      case E2 of let_exp{dec_list=dec_list2,exp=exp2,exp_info=exp_info2} =>
        exp_info=exp_info2 andalso info_exp_eq(exp,exp2) 
        andalso length dec_list=length dec_list2 andalso
        forall(info_dec_eq,combine(dec_list,dec_list2))
      | _ => false
      )
  | as_exp{var,pat,exp_info} => (
      case E2 of as_exp{var=var2,pat=pat2,exp_info=exp_info2} =>
        var=var2 andalso exp_info=exp_info2 andalso info_exp_eq(pat,pat2)
      | _ => false
      )

and info_dec_eq( {func,pat,exp,dec_info} : (''a,''b)d, 
      {func=func2,pat=pat2,exp=exp2,dec_info=dec_info2} 
    : (''a,''b)d ) :  bool =
  func=func2 andalso dec_info=dec_info2 andalso 
  info_exp_eq(pat,pat2) andalso info_exp_eq(exp,exp2)

and info_exp_list_eq([],[]) = true
  | info_exp_list_eq(_,[]) = false
  | info_exp_list_eq([],_) = false
  | info_exp_list_eq(E1::Es1,E2::Es2) = 
      info_exp_eq(E1,E2) andalso info_exp_list_eq(Es1,Es2)

fun rule_eq( { pat, exp, ... } : ('a,'b)rule_type,
      { pat = P, exp = E, ... } : ('a,'b)rule_type ) : bool =
  exp_eq( pat, P ) andalso exp_eq( exp, E )

fun rules_eq( Rs1, Rs2 ) = list_eq( rule_eq, Rs1, Rs2 )


local

structure H = Symbol_HashTable

in

type sym_subst = symbol H.hash_table

local

fun gen_sym_subst_funs( Subst : sym_subst ) =
  let
    fun replace Sym =
      case H.find Subst Sym of
        NONE => Sym
      | SOME Sym => Sym
    fun apply_to_dec( { func, pat, exp, dec_info } : ('a,'b)d ) = {
      func = replace func,
      pat = apply_to_exp pat,
      exp = apply_to_exp exp,
      dec_info = dec_info
      }
    and apply_to_exp E =
      case E of
        app_exp{ func, args, exp_info } =>
          app_exp{ 
            func = replace func,
            args = map( apply_to_exp, args ),
            exp_info = exp_info }
      | case_exp{ exp, rules, exp_info } =>
          case_exp{
            exp = apply_to_exp exp,
            rules = map( fn Rule as { pat, exp, ... } =>
              mk_rule( Rule, apply_to_exp pat,apply_to_exp exp ),
              rules ),
            exp_info = exp_info }
      | let_exp{ dec_list, exp, exp_info } =>
          let_exp{
            dec_list = map( apply_to_dec, dec_list ),
            exp = apply_to_exp exp,
            exp_info = exp_info }
      | as_exp{ var, pat, exp_info } =>
          as_exp{
            var = replace var,
            pat = apply_to_exp pat,
            exp_info = exp_info }
  in
    ( apply_to_dec, apply_to_exp ) 
  end (* fun gen_sym_subst_funs *)

in (* local *)

fun apply_sym_subst( D : ('a,'b)d, Subst : sym_subst ) : ('a,'b)d =
  case gen_sym_subst_funs Subst of ( f, _ ) => f D

fun apply_sym_subst_exp( E : ('a,'b)e, Subst : sym_subst ) : ('a,'b)e =
  case gen_sym_subst_funs Subst of ( _, f ) => f E

end (* local *)
end (* local *)


type ('a,'b) exp_subst = (('a,'b)e*('a,'b)e) list

fun print_exp_subst Subst =
  loop( fn ( From, To ) => (
    Print.print_exp' From; p " -> "; Print.print_exp' To; nl()
    ),
    Subst )

fun apply_exp_subst( E : ('a,'b)e, Subst : (('a,'b)e * ('a,'b)e) list )
    : ('a,'b)e =
  case assoc_opt'(exp_eq,E,Subst) of
    SOME New_E => New_E
  | NONE =>
  let fun a Sub = apply_exp_subst(Sub,Subst) in
    case E of
      app_exp{func,args,exp_info} =>
        app_exp{func=func,args=map(a,args),exp_info=exp_info}
    | case_exp{exp,rules,exp_info} =>
        case_exp{exp=a exp, rules=map(fn Rule as {pat,exp,...} =>
            mk_rule(Rule, pat, a exp),
            rules),
          exp_info=exp_info}
    | let_exp{dec_list,exp,exp_info} =>
        let_exp{dec_list=map(fn{func,pat,exp,dec_info} =>
            {func=func,pat=pat,exp=a exp,dec_info=dec_info},
            dec_list),
          exp=a exp, exp_info=exp_info}
    | as_exp{var,pat,exp_info} =>
        let val Var_subst = flat_map(
          fn(app_exp{func=F1,args=nil,...},app_exp{func=F2,args=nil,...}) =>
              (F1,F2)::nil
          | _ => nil,
          Subst)
          val Var = case assoc_opt(var,Var_subst) of
            NONE => var
          | SOME V => V
        in
          as_exp{var=Var,pat=a pat,exp_info=exp_info}
        end
  end

fun exp_subst_compose( Subst1, Subst2 ) =
  map( fn( From, To ) => ( From, apply_exp_subst( To, Subst2 ) ), Subst1 ) 
  @
  filter( fn( From2, To2 ) => 
    not( exists( fn( From1, To1 ) => exp_eq( From1, From2 ), Subst1 ) ),
    Subst2 )
   
   
fun exp_count( p : ('a,'b)e -> bool, E : ('a,'b)e ) : int =
  let val N = if p E then 1 else 0
      fun ec Sub = exp_count(p,Sub)
  in
    N + (
    case E of
      app_exp{func,args,...} => int_sum(map(ec,args))
    | case_exp{exp,rules,...} => ec exp + int_sum(map(ec o #exp,rules))
    | let_exp{dec_list,exp,...} => ec exp + int_sum(map(ec o #exp,dec_list))
    ) 
  end

fun sym_exp_count( Sym : symbol, E : ('a,'b)e ) : int =
  exp_count( fn app_exp{func,...} => func=Sym | _ => false,E)

fun sym_exp_member( Sym : symbol, E : ('a,'b)e ) : bool =
  exp_count( fn app_exp{func,...} => func=Sym | _ => false,E) >=1


fun exp_filter( p : ('a,'b)e -> bool, E : ('a,'b)e ) : ('a,'b)e list =
  let val Xs = if p E then E::nil else nil
      fun ef Sub = exp_filter(p,Sub)
  in
    Xs @ (
    case E of
      app_exp{func,args,...} => flat_map(ef,args)
    | case_exp{exp,rules,...} => ef exp @ flat_map(ef o #exp,rules)
    | let_exp{dec_list,exp,...} => ef exp @ flat_map(ef o #exp,dec_list)
    | as_exp{var,pat,...} => ef pat
    ) 
  end


fun exp_flat_map( f : ('a,'b)e -> 'c list, E : ('a,'b)e ) : 'c list =
  let fun em Sub = exp_flat_map(f,Sub)
  in
    f E @ (
    case E of
      app_exp{func,args,...} => flat_map(em,args)
    | case_exp{exp,rules,...} => em exp @ flat_map(em o #exp,rules)
    | let_exp{dec_list,exp,...} => em exp @ flat_map(em o #exp,dec_list)
    ) 
  end

fun exp_map( f: ('a,'b)e -> ('a,'b)e, E : ('a,'b)e ) : ('a,'b)e =
  let fun em Sub = exp_map(f,Sub)
  in
    f(
      case E of
        app_exp{func,args,exp_info} =>
          app_exp{func=func,args=map(em,args),exp_info=exp_info}
      | case_exp{exp,rules,exp_info} =>
          case_exp{exp=em exp, rules=
            map(fn Rule as {pat,exp,...} => mk_rule( Rule, pat, em exp),
              rules),
            exp_info=exp_info}
      | let_exp{dec_list,exp,exp_info} =>
          let_exp{dec_list=map(fn{func,pat,exp,dec_info} =>
            {func=func,pat=pat,exp=em exp,dec_info=dec_info},
            dec_list),
            exp=em exp, exp_info=exp_info}
      | as_exp{var,pat,exp_info} =>
          as_exp{var=var,pat=em pat,exp_info=exp_info}
       )
  end
      


fun remove_as Pat = exp_map( 
  fn as_exp{var,pat,exp_info} => app_exp{func=var,args=nil,exp_info=exp_info}
   | Sub => Sub,
  Pat )


fun act_info_loop( update : ('a,'b)rule_type -> unit, E : ('a,'b)e ) 
    : unit =
  let
    fun a Sub = act_info_loop( update, Sub )
  in
  case E of
    app_exp{ args, ... } => loop( a, args )
  | case_exp{ exp, rules, ... } => ( 
      a exp; 
      loop( fn Rule as { exp, ... } => (update Rule; a exp), rules )
      )
  | let_exp{ dec_list, exp, ... } => (
      loop( fn{ exp, ... } => a exp, dec_list );
      a exp
      )
  end



fun exp_info_replace(E,f) =
  case E of 
    app_exp{func,args,exp_info} =>
      app_exp{func=func,args=args,exp_info=f exp_info}
  | case_exp{exp,rules,exp_info} =>
      case_exp{exp=exp,rules=rules,exp_info=f exp_info}
  | let_exp{dec_list,exp,exp_info} =>
      let_exp{dec_list=dec_list,exp=exp,exp_info=f exp_info}
  | as_exp{var,pat,exp_info} =>
      as_exp{var=var,pat=pat,exp_info=f exp_info}
  
exception Match_exception
fun match( ty_var_exp V, Type ) = SOME ( fn _ => raise Match_exception )
  | match( Range as ty_con_exp(FR,ArgsR), Type as ty_con_exp(FT,ArgsT) ) =
(* Returns SOME(substitution function) if Range and Type match and NONE
   otherwise. 
*)
  if Range=Type then
    SOME( fn X => X )
  else if FR=FT then
    case ArgsR of
      (ty_var_exp V)::nil =>
        let fun subst_fun( ty_var_exp W ) =
                  if V=W then hd ArgsT else raise Match_exception
              | subst_fun(ty_con_exp(F,Args)) =
                  ty_con_exp(F,map(subst_fun,Args))
        in
          SOME subst_fun
        end
    | _ => NONE
  else
    NONE
  

type pos = int list

val print_pos = print_int_list
fun print_pos_list Xss = print_list( fn Xs => print_pos Xs, Xss )

fun pos_hash( Xs : pos ) : word =
  Word.fromInt( hash_real_to_int( list_hash( real, Xs ) * 1.0E9 ) )

local

structure Pos_hash_key : HASH_KEY =
struct
  type hash_key = pos
  val hashVal = pos_hash
  fun sameKey( X, Y : pos ) = X = Y
end

in


structure Pos_set = HashSet( Pos_hash_key )
structure Pos_hash = Pos_set.H

local

structure H = Hash_make_set_functor( Pos_hash )

in

val pos_hash_make_set = H.hash_make_set

end (* local *)


end


fun pos_pack( Xs : pos ) = pack( map( Int.toString, Xs ) )

fun pos_unpack( S : string ) : pos =
  map( int_from_string, unpack S )

fun pos_list_pack( Xs : pos list ) : string =
  pack( map( pos_pack, Xs ) )

fun pos_list_unpack( S : string ) : pos list =
  map( pos_unpack, unpack S )

fun is_legal_index( N, Xs ) = 
  not( null Xs ) andalso
  0 <= N andalso N < length Xs

fun is_legal_pos( Pos : pos, E : ( 'a, 'b )e ) : bool =
  case Pos of
    [] => true
  | P :: Pos =>
  case E of
    app_exp{ args, ... } => is_legal_index( P, args ) andalso
      is_legal_pos( Pos, nth( args, P ) )

  | case_exp{ exp, rules, ... } =>
      if P = 0 then is_legal_pos( Pos, exp ) else
      is_legal_index( P-1, rules ) andalso
      is_legal_pos( Pos, #exp( nth( rules, P-1 ) ) )

  | let_exp{ dec_list, exp, ... } =>
      if P = length dec_list then
        is_legal_pos( Pos, exp ) 
      else
        is_legal_index( P, dec_list ) andalso 
        is_legal_pos( Pos, #exp( nth( dec_list, P ) ) )
     

exception Pos_replace
exception Pos_replace_dec
fun pos_replace( Old : ('a,'b)e, Pos : pos, F : ('a,'b)e->('a,'b)e ) 
    : ('a,'b)e =
(
  case Pos of 
    nil => F Old
  | P::Ps => 
  case Old of
    app_exp{func,args,exp_info} =>
      app_exp{func=func, 
        args=list_replace(args,P,pos_replace(nth(args,P),Ps,F)),
        exp_info=exp_info
        }
  | case_exp{exp,rules,exp_info} =>
      if P=0 then
        case_exp{ exp=pos_replace(exp,Ps,F), rules=rules,
          exp_info=exp_info }
      else 
        let val Rule as {pat,exp=Rhs,...} = nth(rules,P-1)
        in
          case_exp{ exp=exp, rules=
            list_replace(rules,P-1,
              mk_rule( Rule, pat, pos_replace(Rhs,Ps,F))),
            exp_info=exp_info }
        end
  | let_exp{dec_list,exp,exp_info} =>
      if P < length dec_list then
        let val New_dec = pos_replace_dec(nth(dec_list,P),Ps,F)
        in
          let_exp{ dec_list = list_replace(dec_list,P,New_dec),
            exp=exp, exp_info=exp_info }
        end
      else
        let_exp{ dec_list=dec_list, exp=pos_replace(exp,Ps,F),
          exp_info=exp_info }
) handle Ex => (
  output( !std_out, "\n\nOld =\n" );
  Print.print_exp' Old;
  output( !std_out, "\nPos =" );
  print_pos Pos;
  re_raise(Ex,"Pos_replace")
  )

and pos_replace_dec( Old as {func,pat,exp,dec_info} : ('a,'b)d, 
    Pos : pos, F : ('a,'b)e->('a,'b)e ) : ('a,'b)d =
  {func=func, pat=pat, exp=pos_replace(exp,Pos,F), 
   dec_info=dec_info
   } handle Ex => re_raise(Ex,"Pos_replace_dec")

fun poses_replace( E, Poses, replace ) =
  case Poses of
    [] => E
  | Pos :: Poses => 
      poses_replace( pos_replace( E, Pos, replace), Poses, replace )
  

fun poses_replace_dec( D, Poses, replace ) =
  case Poses of
    [] => D
  | Pos :: Poses => 
      poses_replace_dec( pos_replace_dec( D, Pos, replace), Poses, replace )
  
exception Pos_fold
fun pos_fold( f : 'c * ('a,'b)e * pos -> 'c, g : ('a,'b)e -> 'c, Pos : pos, 
    E : ('a,'b)e ) : 'c =
(
  case Pos of 
    nil => g E
  | P::Ps => 
  case E of
    app_exp{args,...} =>
      f( pos_fold(f,g,Ps,nth(args,P)), E, Pos )
  | case_exp{exp,rules,...} =>
      if P=0 then
        f( pos_fold(f,g,Ps,exp), E, Pos )
      else 
        f( pos_fold(f,g,Ps,#exp(nth(rules,P-1))), E, Pos )
  | let_exp{dec_list,exp,...} =>
      if P < length dec_list then
        f( pos_fold(f,g,Ps,#exp(nth(dec_list,P))), E, Pos )
      else
        f( pos_fold(f,g,Ps,exp), E, Pos  )
) handle Ex => raise Pos_fold
    



exception Case_subs_at_pos
fun case_subs_at_pos(E,Pos) : (('a,'b)e * ('a,'b)e list) list =
  let fun g _ = nil
      fun f(Case_subs,E_sub,P::_) =
        case E_sub of
          case_exp{exp,rules,...} => 
            ( exp, flat_map(fn {pat,exp,...} => var_exps_in_pat pat, 
                     rules) ) :: 
            Case_subs
        | _ => Case_subs
  in
    pos_fold(f,g,Pos,E)
  end
  handle Ex => re_raise(Ex,"Case_subs_at_pos")

exception Cum_case_subs_at_pos
fun cum_case_subs_at_pos(E,Pos) =
  foldright(
    nil,
    fn( (Case_analyzed_exp,Subs), Cum_case_subs ) =>
      ( Case_analyzed_exp, 
        Subs@flat_map( fn Sub =>(case assoc_opt(Sub,Cum_case_subs) of
                                   NONE => nil
                                 | SOME Subs' => Subs'),
                       Subs ) ) 
      :: Cum_case_subs,
    case_subs_at_pos(E,Pos)
    )
  handle Ex => re_raise(Ex, "Cum_case_subs_at_pos")
        


fun case_analyzed_exps E =
  let val c = case_analyzed_exps in
  case E of
    app_exp{args,...} => flat_map(c ,args)
  | as_exp{var,pat,exp_info} =>
      app_exp{ func=var, args=nil, exp_info=exp_info} :: c pat
  | case_exp{exp,rules,...} => 
      exp::flat_map( fn{pat,exp,...} => c pat @ c exp, rules )
  | let_exp{dec_list,exp,...} =>
      c exp @ flat_map(fn{pat,exp,...} => c pat @ c exp, dec_list )
  end
  
exception Case_analyzed_exps_at_pos
fun case_analyzed_exps_at_pos(E,Pos) =
  let 
    val c = case_analyzed_exps
    fun g _ = nil
    fun f(Es,E,P::_) =
      case E of
        case_exp{exp,rules,...} => 
         if P=0 then exp::Es else exp::c(#pat(nth(rules,P-1)))@Es
      | let_exp{dec_list,...} =>
          if P < length dec_list then
            c(#pat(nth(dec_list,P)))@Es
          else
            Es
      | _ => Es
  in
    pos_fold(f,g,Pos,E)
  end
  handle Ex => re_raise(Ex, "Case_analyzed_exps_at_pos")


exception Pos_to_sub
fun pos_to_sub(E,Pos) =
  let fun g E = E
    fun f(E,_,_) = E
  in
    pos_fold(f,g,Pos,E)
  end
  handle Ex => (
    p"\n\npos_to_sub:\nE =\n";
    Print.print_exp' E;
    p"\nPos = ";
    print_pos Pos;
    raise Pos_to_sub
    )

exception Is_leaf
fun is_leaf_pos(E,Pos) = is_leaf(pos_to_sub(E,Pos))
  handle Ex => re_raise(Ex, "Is_leaf")

fun is_prefix( [], _ ) = true
  | is_prefix( _, [] ) = false
  | is_prefix( P::Prefix, X::Xs ) = P=X andalso is_prefix(Prefix,Xs)

fun prefix_related( Xs, Ys ) = is_prefix( Xs, Ys ) orelse is_prefix( Ys, Xs )

fun is_strict_prefix(Prefix,Xs) = is_prefix(Prefix,Xs) andalso Prefix<>Xs

fun pos_cmp( [], _::_ ) = LESS
  | pos_cmp( _::_, [] ) = GREATER 
  | pos_cmp( X::Xs, Y::Ys ) = 
      if (X:int) < Y then
        LESS
      else if X > Y then
        GREATER
      else
        pos_cmp( Xs, Ys )

fun pos_less( X, Y ) = case pos_cmp( X, Y ) of LESS => true | _ => false


fun pos_list_less( Xs, Ys ) = list_less( pos_less, Xs, Ys )

fun info_map_pos( So_far : pos option,
      f : 'a * pos option -> 'c, g : 'b * pos option -> 'd, 
      E : ('a,'b)e ) : ('c,'d)e =
  let 
    fun et( Sub, Index : int ) = 
      info_map_pos( 
        case So_far of 
          NONE => NONE
        | SOME So_far => SOME( snoc( So_far, Index ) ), 
        f, g, Sub ) 

    fun et' Sub = 
      info_map_pos( NONE, f, g, Sub ) 

    fun dt( D, Index : int ) = 
      info_map_dec_pos( 
        case So_far of
          NONE => NONE
        | SOME So_far => SOME( snoc( So_far, Index ) ), 
        f, g, D ) 
    val f = fn Exp_info => f( Exp_info, So_far )
    val g = fn Dec_info => g( Dec_info, So_far )
  in
  case E of
    app_exp{func,args,exp_info} =>
      app_exp{ 
        func = func, 
        args = map( et, indexize( args, 0 ) ), 
        exp_info = f exp_info 
        }
    | let_exp{ dec_list, exp, exp_info } =>
        let_exp{ 
          dec_list = map( dt, indexize( dec_list, 0 ) ),
          exp=et( exp, length dec_list ),
          exp_info=f exp_info 
          }
    | case_exp{ exp, rules, exp_info } =>
        case_exp{ 
          exp = et( exp, 0 ),
          rules = map( fn( Rule as { pat, exp, ... }, I ) =>
            mk_rule( Rule, et' pat, et( exp, I ) ), 
            indexize( rules, 1 ) ),
          exp_info = f exp_info}
    | as_exp{ var, pat, exp_info } =>
        as_exp{ var = var, pat = et' pat, exp_info = f exp_info }
  end
and info_map_dec_pos( So_far : pos option, 
      f : 'a * pos option -> 'c, g : 'b * pos option -> 'd, 
      { func, pat, exp, dec_info } : ('a,'b)d ) : ('c,'d)d =
  { func = func, 
    pat = info_map_pos( NONE, f, g, pat ), 
    exp = info_map_pos( So_far, f, g, exp),
    dec_info = g( dec_info, So_far ) }

val info_map_pos = fn( f, g, E ) => 
  info_map_pos( SOME [], f, g, E )

val info_map_dec_pos = fn( f, g, D ) =>
  info_map_dec_pos( SOME [], f, g, D )


fun info_map( f : 'a -> 'c, g : 'b -> 'd, E : ('a,'b)e ) : ('c,'d)e =
  info_map_pos( 
    fn( Exp_info, _ ) => f Exp_info,
    fn( Dec_info, _ ) => g Dec_info,
    E )


fun info_map_dec( f : 'a -> 'c, g : 'b -> 'd, 
      D : ('a,'b)d ) : ('c,'d)d =
  info_map_dec_pos( 
    fn( Exp_info, _ ) => f Exp_info,
    fn( Dec_info, _ ) => g Dec_info,
    D )
      
fun remove_types E = info_map(
  fn _ => Ast.no_exp_info(),
  fn _ => Ast.no_dec_info(),
  E )

fun remove_types_of_dec D = info_map_dec(
  fn _ => Ast.no_exp_info(),
  fn _ => Ast.no_dec_info(),
  D )


fun exp_hash(E:('a,'b)e) : real =
  let
   val Rand = Random.rand( 712747126, ~544732623 )
   fun h_list nil =  0.41938726363625387376254510732
     | h_list(X::Xs : real list) = 
         normrealhash' X + normrealhash'( h_list Xs * Random.randReal Rand )
    fun exp_hash'(E : ('a,'b)e) : real =
    case E of
      app_exp{func,args,...} =>
        h_list( 0.61245687719368 :: real_symbol_hash func :: 
                map(exp_hash',args))
    | case_exp{exp,rules,...} =>
        h_list( 0.196281736161938 :: map(exp_hash',exp::map(#exp,rules)))
    | let_exp{dec_list,exp,...} =>
        h_list( 0.3284927263812937325 :: map(exp_hash',exp::map(#exp,dec_list)))
  in
    exp_hash' E 
  end
  handle Ex => (
    nl();nl();
    Print.print_exp' E;
    re_raise(Ex,"Exp_hash")
    )




local

structure Exp_hash_key : HASH_KEY =
struct
  type hash_key = exp
  fun hashVal X = hash_real_to_word( exp_hash X )
  fun sameKey( X, Y : exp )= exp_eq( X, Y )
end

in

structure Exp_HashTable = HashTableFn(Exp_hash_key)

end (* local *)


local

structure H = Hash_make_set_functor( Exp_HashTable )

in

val exp_hash_make_set = H.hash_make_set

end (* local *)


(* Function used for commutativity rejection: *)
fun app_exp_less( app_exp{ func=F1, args=Args1, ...} : ('a,'b)e, 
                  app_exp{ func=F2, args=Args2, ...} ) =
      symbol_less(F1,F2) orelse F1=F2 andalso 
      app_exp_list_less(Args1,Args2)
  | app_exp_less( E1, E2 ) = exp_hash E1 < exp_hash E2
and app_exp_list_less(Xs,Ys) =
  case (Xs,Ys) of
    (nil,nil) => false
  | (nil,_) => true
  | (_,nil) => false
  | (X1::Xs1,Y1::Ys1) => app_exp_less(X1,Y1) orelse 
      exp_eq(X1,Y1) andalso app_exp_list_less(Xs1,Ys1)

fun adjust_cost_limits( 
      emit : ( real option list -> real option list ) * int * real list -> 
             real list,
      Kinds : int list,
      Xs : ( real * real list ) list
      ) : unit =
(* emit( post_adjust, Kind, Cost_limits ) -> Consumed interval widths,
   where a consumed interval width belongs to the full interval [0,1].
   Xs = [ ( Cost limit, Weights ), ... ]
*)
  case Kinds of
    [] => ()
  | Kind :: Kinds =>
  let
    val Cost_limits = map( fn( Cost_limit, W :: _ ) => Cost_limit * W, Xs )
    fun post_adjust( Cost_opts : real option list ) =
      map( fn( Opt, ( _, W :: _ ) ) =>
        case Opt of NONE => NONE | SOME Cost => SOME( Cost / W ),
        combine( Cost_opts, Xs ) )
    val Consumptions = emit( post_adjust, Kind, Cost_limits )
    val Xs = map( fn( ( Cost_limit, W :: Weights ), Consumption ) =>
      ( Cost_limit, 
        case real_sum Weights of Remaining =>
        map( fn W1 => W1 * ( 1.0 + ( W - W * Consumption ) 
                      / Remaining ),
             Weights )
        ),
      combine( Xs, Consumptions ) )
  in
    adjust_cost_limits( emit, Kinds, Xs )
  end



datatype 'a exec_result =
  ? | too_many_calls | some of 'a

datatype output_eval_type = correct | wrong | dont_know | overflow

end (* structure Ast_lib *)
