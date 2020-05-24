(*
File: type.sml.
Created: 1993-05-24.
Modified: 2000-03-24.

2000-03-24: Overloading with alternative types int and real 
  for *, +, -, ... added.

Type Inference
--------------
See The Implementation of Functional Programming Languages, Simon L. 
Peyton-Jones, Prentice-Hall, 1987.
*)

signature TYPE =
sig

val infer_types_of_decs : Ast.dec list * Ast.ty_env -> Ast.dec list
val infer_types_of_dec_using_schema : 
      Ast.dec * Ast.ty_schema * Ast.ty_env -> Ast.dec
val infer_types_of_exp : Ast.exp * Ast.ty_env -> Ast.exp
val parse_dec_t : string * string * Ast.ty_env -> Ast.dec
val parse_exp_t : string * string * Ast.ty_env -> Ast.exp

end

structure Type : TYPE =
struct

open Lib List1 Ast Ast_lib Print

exception Tc of int

type eq_set = ( ty_exp * ty_exp ) list

type subst = ( ty_var * ty_exp ) list

fun apply_subst( E, Subst ) =
  case E of
    ty_var_exp V =>
      ( case assoc_opt(V,Subst) of NONE => ty_var_exp V | SOME E => E )
  | ty_con_exp( Ty_con, Args ) => 
      ty_con_exp( Ty_con, map( fn Arg => apply_subst(Arg,Subst), Args ) )

fun subst_comp( Subst1, Subst2 ) =
  map( fn(V,E) => ( V, apply_subst(E,Subst2) ), Subst1 ) @
  filter( fn(V2,E2) => not( exists( fn(V1,E1) => V1=V2, Subst1 ) ),
          Subst2
          )

fun occurs(V,E) = 
  case E of ty_var_exp V1 => V=V1
  | ty_con_exp(_,Args) => exists( fn A => occurs(V,A), Args )
 
(* See Bjorn Kirkeruds notes for the course in rewrite systems, which contain
   the unification algorithm given below.
*)

fun mgu_eq_set( Ps : eq_set, Sigma : subst ) : subst option =
  case Ps of nil => SOME Sigma
  | (E1,E2)::Ps1 =>
  case E1 of ty_var_exp V1 =>
    if E1=E2 then (* Delete *)
      mgu_eq_set(Ps1,Sigma)
    else if occurs(V1,E2) then (* Check *)
      NONE
    else (* Eliminate *)
      let  val Rho = (V1,E2)::nil in
        mgu_eq_set(
          map( fn(E1,E2) => ( apply_subst(E1,Rho), apply_subst(E2,Rho) ),
               Ps1 ),
          subst_comp(Sigma,Rho)
          )
      end
  | ty_con_exp(Ty_con1,Args1) => 
  case E2 of ty_var_exp V2  => (* Orient *) 
    mgu_eq_set( (E2,E1)::Ps1, Sigma )
  | ty_con_exp(Ty_con2,Args2) =>
  if Ty_con1 = Ty_con2 then (* Decompose *)
    mgu_eq_set( combine(Args1,Args2) @ Ps1, Sigma )
  else (* Conflict *)
    NONE


fun apply_subst_to_schema( {schematic_vars,ty_exp} : ty_schema, 
                           Subst : subst ) : ty_schema =
  if not( null( intersection( schematic_vars, map(#1,Subst) ) ) ) then
    raise Internal_error
  else
    { schematic_vars=schematic_vars, ty_exp=apply_subst(ty_exp,Subst) }

fun apply_subst_to_ty_env( Type_env, Subst ) =
  map( fn (Id,Sch) => (Id,apply_subst_to_schema(Sch,Subst)), Type_env )

fun apply_subst_to_root( E, Subst ) =
  case E of 
    app_exp{func,args,exp_info} =>
      app_exp{ func=func, args=args, 
        exp_info=set_ty_exp( exp_info, 
          apply_subst(get_ty_exp exp_info,Subst) ) }
  | case_exp{exp,rules,exp_info} =>
      case_exp{ exp=exp, rules=rules, 
        exp_info=set_ty_exp( exp_info,
          apply_subst(get_ty_exp exp_info,Subst) ) }
  | let_exp { dec_list,exp,exp_info} =>
      let_exp { dec_list=dec_list, exp=exp,
        exp_info=set_ty_exp( exp_info,
          apply_subst(get_ty_exp exp_info,Subst) ) }
  | as_exp {var,pat,exp_info} =>
      as_exp{ var=var, pat=pat,
        exp_info=set_ty_exp( exp_info,
          apply_subst(get_ty_exp exp_info,Subst) ) }
                
fun apply_subst_to_exp( E, Subst ) =
let val a =  fn E => apply_subst_to_exp(E,Subst) in
  case E of 
    app_exp{func,args,exp_info} =>
      app_exp{ func=func, args=map(a,args), 
        exp_info=set_ty_exp( exp_info,
          apply_subst(get_ty_exp exp_info,Subst) ) }
  | case_exp{exp,rules,exp_info} =>
      case_exp{ 
        exp=apply_subst_to_exp(exp,Subst), 
        rules=map( fn Rule as {pat,exp,...} => 
          mk_rule( Rule, a pat, a exp), 
          rules ),
        exp_info=set_ty_exp( exp_info,
          apply_subst(get_ty_exp exp_info,Subst) ) }
  | let_exp { dec_list,exp,exp_info} =>
      let_exp{ 
        dec_list=map( fn{func,pat,exp,dec_info=Sch} =>
                   {func=func, pat=a pat, exp=a exp,
                    dec_info=apply_subst_to_schema(Sch,Subst)
                    },
                   dec_list),
        exp = a exp,
        exp_info=set_ty_exp( exp_info,
          apply_subst(get_ty_exp exp_info,Subst) ) }
  | as_exp {var,pat,exp_info} =>
      as_exp{ var=var, pat=a pat,
              exp_info=set_ty_exp( exp_info,
          apply_subst(get_ty_exp exp_info,Subst) ) }
  end
                
fun new_instance{ schematic_vars, ty_exp } =
let val Renamed_schematic_vars = 
  map( fn V => gen_ty_var_sym(), schematic_vars )
in
  { schematic_vars=Renamed_schematic_vars,
    ty_exp=apply_subst( ty_exp,
                        combine(
                          schematic_vars,
                          map( fn N => ty_var_exp N, Renamed_schematic_vars )
                          )
                        )
    }
end

exception Assoc_ty_env
fun assoc_ty_env( F:symbol, Ty_env:ty_env ) =
  if is_int F then 
    { schematic_vars = [], ty_exp = ty_con_exp( INT, [] ) }
  else if is_real F then 
    { schematic_vars = [], ty_exp = ty_con_exp( REAL, [] ) }
  else
  case assoc_opt(F,Ty_env) of
    SOME X => X
  | NONE => (
      output(!std_err,
        "\n\nSymbol " ^ symbol_to_string F ^ " not found in ");
      Print.print_ty_env Ty_env;
      raise Assoc_ty_env
      )



(* The main function to be defined is
   tc( Type_env : ty_env, E : exp ) : ( subst * exp );
   Type_env associates a type schema with each free variable in E. It is
   assumed that the variables in E have unique names.
   Type_env initially contains type schemas for pre-defined identifiers.
   Let (Phi,E_typed) be tc's return value. E_typed is E with a type in each 
   node. Only the type in the root of E_typed is guarenteed to be fully 
   instantiated. Phi needs to be applied to all types in E_typed in order
   to obtain a correctly typed expression.
   The exception Tc is raised if E is mis-typed.
   The function tcl differs from tc in that it operates on a list of
   expressions.
*)


fun tcl( Type_env : ty_env, Es : exp list ) : subst * (exp list) =
  case Es of nil => (nil,nil)
  | E1::Es1 =>
  case tc(Type_env,E1) of (Phi,E1_typed) =>
  case tcl( apply_subst_to_ty_env(Type_env,Phi), Es1 ) of (Psi,Es1_typed) =>
    ( subst_comp(Phi,Psi), apply_subst_to_root(E1_typed,Psi)::Es1_typed )

and tc( Type_env : ty_env, E : exp ) : subst * exp =
case E of
  app_exp{ func=F, args=As, ... } =>
  ( case As of nil =>
        ( nil,
          app_exp{  
            func=F, args=nil, 
            exp_info= mk_exp_info(
              if is_int F then
                ty_con_exp( INT, [] )
              else if is_real F then
                ty_con_exp( REAL, [] )
              else
                #ty_exp(new_instance(assoc_ty_env(F,Type_env)))) }
          ) 
    | _ =>
    let val (Phi,As_typed) = tcl(Type_env,As)
    in
      if F=TUPLE then
        ( Phi,
          app_exp{
            func=F, args=As_typed, exp_info = mk_exp_info(
              ty_con_exp( TUPLE_TY_CON , map(type_of_exp,As_typed) )
              )
            }
          )
      else
  let 
    val F =
      if sym_is_overloaded F andalso exists( fn A =>
        type_of_exp A = ty_con_exp( REAL, [] ),
        As_typed )
      then
        get_real_overloaded_sym F
      else 
        F
        
    val ty_con_exp( THIN_ARROW, Ty1::Ty2::nil ) = 
        #ty_exp(new_instance(assoc_ty_env(F,Type_env))) 
    in
      case mgu_eq_set( 
   (Ty1, if null(tl As_typed ) then 
          type_of_exp(hd As_typed) 
         else   
           ty_con_exp(TUPLE_TY_CON,map(type_of_exp,As_typed))
    ) :: nil,
   Phi
   ) of
        NONE => raise Tc 1
      | SOME Psi =>
          ( Psi,
            app_exp{
              func=F, args=As_typed, 
              exp_info = mk_exp_info(apply_subst(Ty2,Psi))
              }
            )
    end end
    )
| as_exp{ var=V, pat=P, ... } =>
(* Unify the type of V with the type of P *)
  let val (Phi,P_typed) = tc(Type_env,P)
      val Ty_exp = apply_subst( #ty_exp(new_instance(assoc_ty_env(V,Type_env))), Phi )
  in
    case mgu_eq_set( (Ty_exp,type_of_exp(P_typed))::nil, Phi ) of
      NONE => raise Tc 2
    | SOME Psi => 
        ( Psi, 
          as_exp{ var=V, pat=P_typed, 
                  exp_info = mk_exp_info(apply_subst(Ty_exp,Psi))
                  }
          )
  end
| case_exp{ exp=E, rules=Rs, ... } =>
(* Assume that Rs has the form P1=>E1 | P2=>E2 ... .
   The types of [E,P1,P2,...] must be the same.
   The types of [E1,E2,...] must also be the same.
   The first step is to associate a fresh type schema with each variable
   in [P1,P2,...].
*)
let val Es = map( #exp, Rs )
    val Ps = map( #pat, Rs )
in
let val All_vars : symbol list = flat_map( vars_in_pat, Ps ) in
let val New_ty_env =
    map( 
      fn V => (V,{ schematic_vars = nil, 
                   ty_exp = ty_var_exp(gen_ty_var_sym()) }),
      All_vars
      ) @ Type_env
in
let 
  val (Phi,E_Ps_typed) = tcl( New_ty_env, E::Ps )
  val Phi = 
    case map( type_of_exp, E_Ps_typed ) of E_Ps_types =>
    case mgu_eq_set( combine( tl E_Ps_types, lt E_Ps_types ), Phi ) of
      NONE => raise Tc 99
    | SOME Phi => Phi
in 
(*
p"\nE_Ps_typed = \n";
loop( fn E => (Print.print_exp E; nl() ), E_Ps_typed );
*)
let val (Psi,Es_typed) = 
   let val Ty_env = apply_subst_to_ty_env(New_ty_env,Phi) in
     tcl(Ty_env,Es) 
   end
in
let val E_Ps_types = map( fn E => apply_subst(type_of_exp(E),Psi), E_Ps_typed )
in
let val Es_types = map( type_of_exp, Es_typed )
in 
  case mgu_eq_set(
         combine( tl(E_Ps_types), lt(E_Ps_types) )  @
           combine( tl(Es_types), lt(Es_types) ) ,
         subst_comp(Phi,Psi)
         )  of
    NONE => raise Tc 3
  | SOME Rho =>
      ( Rho,
        case_exp{ 
          exp = hd(E_Ps_typed),
          rules =  map( fn (P,E) => mk_new_rule(P,E),
                        combine(tl(E_Ps_typed),Es_typed) ),
          exp_info = mk_exp_info(apply_subst(type_of_exp(hd(Es_typed)),Rho))
          }
        )
end end end end end end end
| let_exp{ dec_list, exp, ... } =>
(* Assume that the declarations in dec_list have the form
   fun F1 P1 = E1  fun F2 P2 = E2  ... .
   If the type of Fi is Si -> Ti, type(Pi) = Si and type(Ei) = Ti.
   The first step is to associate a fresh type schema with each Fi and
   with each variable in each Pi.
*)
let val Ps = map( #pat, dec_list )
    val Es = map( #exp, dec_list )
    val Fs = map( #func, dec_list )
in
let val Type_env_funs =
    map( fn F => 
      case assoc_opt(F,Type_env) of NONE =>
      ( F,
        { schematic_vars = nil, 
          ty_exp = 
            ty_con_exp( 
              THIN_ARROW, 
              ty_var_exp(gen_ty_var_sym()) ::
              ty_var_exp(gen_ty_var_sym()) :: nil
              )
          })
      | SOME Sch => (F,Sch),
      Fs
      )
    val Type_env_pats =
    map( 
      fn V => ( V, { schematic_vars=nil, 
                     ty_exp=ty_var_exp(gen_ty_var_sym()) } ),
      flat_map(vars_in_pat,Ps)
      )
in
let val New_ty_env = Type_env_funs @ Type_env_pats @ Type_env
in
let 
  val (Phi,Ps_typed) = tcl( New_ty_env,
    map( fn{func, pat, ... } => app_exp{ func = func, args = [pat],
      exp_info = no_exp_info() },
      dec_list ) )
  (* 2000-03-26: Was: tcl(New_ty_env,Ps) *)

  val Ps_typed = map( fn app_exp{ args=[P_typed], ... } => P_typed, Ps_typed )
in
let val (Psi,Es_typed) = tcl( apply_subst_to_ty_env(New_ty_env,Phi), Es )
in
let val Phi_Psi = subst_comp(Phi,Psi)
in
let val Ps_types = map( fn E => apply_subst(type_of_exp(E),Psi), Ps_typed )
    val Es_types = map( type_of_exp, Es_typed )
    val S_types = 
      map( fn( _, { ty_exp=ty_con_exp(THIN_ARROW,S::_::nil),... } ) => 
             apply_subst(S,Phi_Psi),
           Type_env_funs
           )
    val T_types = 
      map( fn( _, { ty_exp=ty_con_exp(THIN_ARROW,_::T::nil),... } ) => 
             apply_subst(T,Phi_Psi),
           Type_env_funs
           )
in
case mgu_eq_set( combine(Ps_types,S_types) @ combine(Es_types,T_types),
                 Phi_Psi
                 ) of
  NONE => raise Tc 4
| SOME Rho =>
(* Compute new schemas for Fs and use them to construct Next_ty_env.
   Let (Phi,E_typed) = tc(Next_ty_env,exp).
   Return subst_comp(Rho,Phi)
*)
let val Next_ty_env' = apply_subst_to_ty_env( Type_env, Rho )
in
let val All_unknowns =
  flat_map( fn( _, {schematic_vars,ty_exp} ) =>
              difference( vars_in_ty_exp(ty_exp), schematic_vars ),
            Next_ty_env'
            )
in
let val Old_Fs_schemas = map( #2, Type_env_funs )
in let val New_Fs_schemas = map( fn Sch => apply_subst_to_schema(Sch,Rho),
                                 Old_Fs_schemas )
(* This code was commented out in order to ensure that all types are
   monomorphic.
  map( 
    fn {schematic_vars,ty_exp} =>
      let val New_ty_exp = apply_subst(ty_exp,Rho) in
        new_instance{ 
          schematic_vars = difference( vars_in_ty_exp(New_ty_exp),
                                       All_unknowns ),
          ty_exp = New_ty_exp
          }
      end,
    Old_Fs_schemas
    )
*)
in
let val Next_ty_env = combine(Fs,New_Fs_schemas) @ Next_ty_env' 
in
let val (Phi,E_typed) = tc(Next_ty_env,exp)
in
( subst_comp(Rho,Phi),
  let_exp{ 
    dec_list =
      map( fn( (F,P), (E,Sch) ) => 
             { func=F, pat=P, exp=E, dec_info=Sch },
           combine( combine(Fs,Ps_typed), combine(Es_typed,New_Fs_schemas) )
           ),
    exp = E_typed,
    exp_info = mk_exp_info(type_of_exp(E_typed))
    }
    )
end end end end end 
end end end end end 
end end end
      

                        







fun tc_start( Type_env : ty_env, E : exp ) : subst * exp =
( 
  tc(Type_env,E)
  )

fun infer_types_of_exp( E:exp, Ty_env : ty_env ) : exp =
case tc_start(Ty_env,E) of
  (Subst,E) => apply_subst_to_exp(E,Subst)


(* The user of the inference system may provide a type for the
   function to be inferred and a function declaration with which to start.
   The right hand side of this function declaration is normally "?"
   but may be different during testing and debugging.
   The function below is called with the user provided function type
   and declaration.
*)

fun infer_types_of_dec_using_schema( D : dec, Sch : ty_schema, 
      Ty_env : ty_env ) : dec =
  let val LE =
    let_exp{ 
         dec_list = D::nil,
         exp = 
           gen_dont_know_exp(
             mk_exp_info(ty_var_exp(gen_ty_var_sym()))
             ),
         exp_info = no_exp_info()
         } 
    val Q_syms = exp_flat_map( 
      fn app_exp{ func, ... } => 
           if is_q func then func::nil  else nil
       | _ => nil,
      LE )
  val Q_syms_ty_env = map(fn Q_sym => 
    (Q_sym,{schematic_vars=nil,ty_exp=ty_var_exp(gen_ty_var_sym())}),
    Q_syms )
in
  case tc_start( (#func D,Sch)::Q_syms_ty_env@Ty_env, LE ) of
    ( Sigma, Let_exp) =>
  case apply_subst_to_exp(Let_exp,Sigma) of
    let_exp{ dec_list = New_D :: nil, ...  } =>
      New_D
end


fun infer_types_of_decs( Ds : dec list, Ty_env : ty_env ) 
    : dec list =
  let val LE =
    let_exp{ 
         dec_list = Ds,
         exp = 
           gen_dont_know_exp(
             mk_exp_info(ty_var_exp(gen_ty_var_sym()))
             ),
         exp_info = no_exp_info()
         } 
    val Q_syms = exp_flat_map( 
      fn app_exp{ func, ... } => 
           if is_q func then func::nil else nil
       | _ => nil,
      LE )
  val Q_syms_ty_env = map(fn Q_sym => 
    (Q_sym,{schematic_vars=nil,ty_exp=ty_var_exp(gen_ty_var_sym())}),
    Q_syms )
in
  case tc_start( Q_syms_ty_env@Ty_env, LE ) of
    ( Sigma, Let_exp) =>
  case apply_subst_to_exp(Let_exp,Sigma) of
    let_exp{ dec_list, ...  } => dec_list
end

fun parse_dec_t( Dec : string, Ty_exp : string, Ty_env : ty_env ) 
    : dec =
let val Dec = Parse.parse_dec(Dec)
    val Ty_exp = Parse.parse_ty_exp(Ty_exp)
in
  infer_types_of_dec_using_schema(
    Dec,
    {schematic_vars=vars_in_ty_exp(Ty_exp), ty_exp=Ty_exp},
    Ty_env
    )
end

fun parse_exp_t( Dec, Ty_exp, Ty_env ) =
  case parse_dec_t(Dec,Ty_exp,Ty_env) of {exp,...} => exp



fun contains_ty_var_sym( ty_var_exp _ ) = true
  | contains_ty_var_sym( ty_con_exp( Sym, TEs ) ) =
      is_ty_var Sym orelse exists( contains_ty_var_sym, TEs )

fun contains_ty_var_sym'( { schematic_vars, ty_exp } : ty_schema ) : bool =
  not( null schematic_vars ) orelse contains_ty_var_sym ty_exp

exception Not_monomorphic_exn
fun check( TE ) : unit =
  if contains_ty_var_sym TE then
    raise Not_monomorphic_exn
  else
    ()

fun check'( Sch ) : unit =
  if contains_ty_var_sym' Sch then
    raise Not_monomorphic_exn
  else
    ()

fun monomorphic_check( E : exp ) : unit =
  ( info_map( check, check', E ); () )
  handle Ex => (
    p"\nmonomorphic_check:\n";
    Print.print_exp E; nl();
    Print.print_exp' E; nl();
    raise Ex )


fun monomorphic_check_dec( D : dec ) : unit =
  ( info_map_dec( check, check', D ); () )
  handle Ex => (
    p"\nmonomorphic_check_dec:\n";
    Print.print_dec D; nl();
    Print.print_dec' D; nl();
    raise Ex )


(*
val infer_types_of_decs : Ast.dec list * Ast.ty_env -> Ast.dec list
val infer_types_of_dec_using_schema : 
      Ast.dec * Ast.ty_schema * Ast.ty_env -> Ast.dec
val infer_types_of_exp : Ast.exp * Ast.ty_env -> Ast.exp
val parse_dec_t : string * string * Ast.ty_env -> Ast.dec
val parse_exp_t : string * string * Ast.ty_env -> Ast.exp
*)
val infer_types_of_decs = 
  fn X => ( case infer_types_of_decs X of Ds =>
    ( loop( monomorphic_check_dec, Ds ); Ds )
    ) 
handle Ex => (
  p"\ninfer_types_of_decs:\n";
  print_decs'( #1 X );
  re_raise( Ex, "infer_types_of_decs" ) )

val infer_types_of_dec_using_schema = 
  fn X => ( case infer_types_of_dec_using_schema X of D =>
    ( monomorphic_check_dec D; D ) )
handle Ex => (
  p"\ninfer_types_of_dec_using_schema:\n";
  print_dec'( #1 X );
  re_raise( Ex, "infer_types_of_dec_using_schema" ) )

val parse_dec_t = 
  fn X => (case parse_dec_t X of D => ( monomorphic_check_dec D; D ) )
handle Ex => (
  p"\nparse_dec_t:\n";
  p( #1 X ); p"\n\n"; p( #2 X ); nl();
  re_raise( Ex, "infer_types_of_dec_using_schema" ) )


val infer_types_of_exp = 
  fn X => (case infer_types_of_exp X of E => ( monomorphic_check E; E ) )
handle Ex => (
  p"\ninfer_types_of_exp :\n";
  print_exp'( #1 X );
  re_raise( Ex, "infer_types_of_exp" ) )



val parse_exp_t = 
  fn X => (case parse_exp_t X of E => ( monomorphic_check E; E ) )
handle Ex => (
  p"\nparse_dec_t:\n";
  p( #1 X ); p"\n\n"; p( #2 X ); nl();
  re_raise( Ex, "infer_types_of_dec_using_schema" ) )

          
 
end (* structure Type *)
