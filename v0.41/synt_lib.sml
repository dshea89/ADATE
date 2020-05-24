(* File: synt_lib.sml.
   Created: 1993-07-19.
   Modified: 2002-11-13.
*)


signature SYNT_LIB =
sig

structure Evaluate : EVALUATE
(* structure NN_opt : NN_OPT *)

val initialize : string -> unit
val initialize_approximate_synt_time_per_exp : unit -> unit

val synt_and_eval_time_per_exp : unit -> real
val approximate_synt_time_per_exp : unit -> real

val construct_case_exp : Ast.ty_exp * Ast.exp -> Ast.exp

val raise_print_dec : Ast.dec -> unit

val get_simplify_count : unit -> int
val get_eval_count : unit -> int

val add_not_activated_exps : ('a,'b)Ast.e -> ('a,'b)Ast.e 
val remove_all_q_case_exps : ('a,'b)Ast.e -> ('a,'b)Ast.e 
val dead_code_elim 
    : Ast.dec -> Ast.dec * Evaluate.program_eval_type option
val dead_code_elim' : ('1a,'1b)Ast.d -> ('1a,'1b)Ast.d
val case_beta_expansion : ('1a,'1b)Ast.e -> ('1a,'1b)Ast.e * bool
val beta_simplify_dec : ('1a,'1b)Ast.d -> 
      ( ('1a,'1b)Ast.d * Evaluate.program_eval_type option ) option
val scope_check : ('a,'b)Ast.e * Ast.symbol list * Ast.symbol list -> bool
val scope_check_dec : ('a,'b)Ast.d -> bool
(* val correctly_typed : Ast.dec -> bool *)
val type_check_dec_raise : Ast.dec -> unit
val add_not_activated_exps_time : unit -> real

val simplify_loop : Ast.dec -> Ast.dec

end (* sig *)


functor Synt_lib_functor( structure Spec : SPEC ) : SYNT_LIB =
struct
open Lib List1 Ast Ast_lib Print
structure Evaluate = Evaluate_functor(structure Spec=Spec)

structure M = Mono_type_fn( Evaluate )
val type_check_dec_raise = M.type_check_dec_raise



(*
Here is a simplified version of the expression synthesis function. This
version assumes that there only is a single, monomorphic type.
This version is included for documentation and benchmarking purposes.
The components to be used for synthesis are given in a list of the form
[ ( "f1", [(),(),()] ), ( "f2", [] ), ... ], where the arity of f1
is 3 and the arity of f2 is 0.

*)

structure Simple_exp_synt :
sig
val bm : int -> int
end =
struct


local

  fun exp_size'( app_exp{ args, ... } :: Es, Rest, A ) =
        exp_size'( Es, args :: Rest, A+1 )
    | exp_size'( [], Exps :: Rest, A ) =
        exp_size'( Exps, Rest, A )
    | exp_size'( [], [], A ) = A

in
  fun exp_size E = exp_size'( [E], [], 0 )
end

(* Main function : *)

fun synt_n(N,Components) =
let

fun synt( S_max : int, Components : (symbol * unit list) list,
          emit : exp -> unit, continue : unit -> bool ) =
(* Calls emit(E1), emit(E2),... emit(En), where E1,E2,... En are synted exps,
   while continue() = true. E1,..., En are all exps of size <= S_max.
*)
if S_max <= 0 then
  ()
else
  while_list(
    continue,
    Components,
    fn (F,Domain_type) =>
      synt_list( Domain_type, S_max-1, Components,
        fn Es => emit(app_exp{ func=F, args=Es, exp_info=Dummy_ty_exp }),
        continue
        )
    )

and synt_list(Types,S_max,Components,emit,continue) =
  case Types of
    nil => emit nil
  | T1::Ts1 =>
  if S_max <= 0 then (* This if-test is only an optimization to prevent an 
                        unnecessary but harmless call to synt. *)
    ()
  else
      synt( S_max-length(Ts1), Components,
        fn E =>
          synt_list( Ts1, S_max-exp_size(E), Components,
            fn Es => emit(E::Es),
            continue
            ),
        continue
        )

val So_far = ref 0
fun continue() = !So_far<N
fun emit(E) = inc So_far
in
  while_list(
    continue,
    fromto(1,1000),
    fn S => synt( S, Components,
              fn E => emit E,
              continue
              )
    );
  !So_far
end (* synt_n *)
  
(* Test data: *)
val X = string_to_symbol( var_sym, "x" )
val G = string_to_symbol( func_sym, "g" )
val Components = [ 
  ( X, [] ), 
  ( G, [(),()] )
  ]

fun bm N = synt_n(N,Components)

end (* structure Simple_exp_synt *)



val Approximate_synt_time_per_exp = ref(~1.0E30)
val Approximate_synt_time_per_exp_initialized = ref false
exception Approximate_synt_time_per_exp_not_initialized

local

fun deepenCount Count =
  let 
    val true = 0 < Count andalso Count < Max_int
    val Timer = mk_timer "initialize_approximate_synt_time_per_exp"
    fun g() = for( 1, Count, fn _ => Simple_exp_synt.bm 100000 )  
    val () = ( start_timer Timer; g() )
    val T = check_timer Timer 
  in
    delete_timer Timer; 
    if T > 5.0 then 
      T / real Count
    else
      deepenCount( 2 * Count ) 
  end

in (* local *)

fun initialize_approximate_synt_time_per_exp () = (
  Approximate_synt_time_per_exp := 0.002 / 0.54 * deepenCount 1;
  Approximate_synt_time_per_exp_initialized := true;
  output(!std_out,"\n\nApproximate_synt_time_per_exp = " ^ 
    Real.toString(!Approximate_synt_time_per_exp) ^
    "\n\n");
  flush_out( !std_out )
  )

end (* local *)

fun approximate_synt_time_per_exp() = (
  if !Approximate_synt_time_per_exp_initialized  then
    !Approximate_synt_time_per_exp
  else
    raise Approximate_synt_time_per_exp_not_initialized)


fun synt_and_eval_time_per_exp() = (
  if !Approximate_synt_time_per_exp_initialized  then
  (!Approximate_synt_time_per_exp) + 
  Evaluate.cum_eval_time() / (Evaluate.no_of_evaluations()+0.1) 
  else
    raise Approximate_synt_time_per_exp_not_initialized)
  handle Ex => re_raise(Ex, "Synt_and_eval_time_per_exp")

fun initialize Spec_file =  Evaluate.initialize Spec_file
  
  

local

exception Alt_to_pat
fun alt_to_pat( Type : ty_exp, 
      { constr : symbol, domain : ty_exp option } ) : exp =
  case domain of
    NONE => app_exp{ func = constr, args = nil, exp_info = Type }
  | SOME( TE as ty_con_exp( Ty_con, Ty_args ) ) =>
  let
    val Ty_args =
      if Ty_con = TUPLE_TY_CON then
        Ty_args
      else
        case Ty_args of
          nil => [TE]
        | _ => raise Alt_to_pat
  in
    app_exp{ func = constr, 
      args = map( fn Ty_arg as ty_con_exp( Ty_con, nil ) =>
        Predefined.mk_pattern Ty_arg, Ty_args ),
      exp_info = Type }
  end

fun analyzed_type_to_pats( Type as ty_con_exp( Ty_con, Ty_args ) ) 
    : exp list =
  if Ty_con = INT orelse Ty_con = REAL 
     orelse Predefined.is_abstract_type Ty_con then
    [ gen_var_exp Type ]
  else if Ty_con = TUPLE_TY_CON then
    [ Predefined.mk_pattern Type ]
  else
  let
    val { alts, ... } : datatype_dec = Predefined.find_datatype_dec Ty_con
  in
    map( fn Alt => alt_to_pat( Type, Alt ), alts )
  end

exception Construct_case_exp

in

fun construct_case_exp( Type : ty_exp,
      E as app_exp{ func, args, 
             exp_info = E_type as ty_con_exp( Constr, _ ) } ) =
  let
    val Pats = analyzed_type_to_pats E_type
    val Rules = map( fn Pat => mk_new_rule( Pat,  Predefined.proper_dummy_exp Type ), Pats )
  in
    case_exp{ exp = E,  rules = Rules, exp_info = Type }
  end
  | construct_case_exp( Type, E ) = (
      output( !std_out, "\n\nconstruct_case_exp:\n" );
      print_ty_exp Type;
      nl();
      print_exp E;
      raise Construct_case_exp
      )
       
end (* local *)




fun raise_print_dec D =
(print_dec' D;
 output(!std_out,"\n\nTYPED\n");
 print_dec D;
 output(!std_out,"\nTYPED\n")
 )
       
fun not_act_to_dont_know E =
  if is_not_activated_exp E then
    gen_dont_know_exp( get_exp_info E )
  else
    E

fun not_act_to_dont_know_dec( { func, pat, exp, dec_info } : ('a,'b)d ) =
  { func = func, pat = pat, exp = not_act_to_dont_know exp,
    dec_info = dec_info }

fun contains_case_exp E = exp_count( is_case_exp, E ) > 0


val Dangerous = ref false

fun contains_f_or_g E =
 exp_count(
   fn app_exp{ func, ... } => 
        is_function func andalso (
        func = F orelse not( is_predefined_sym func ) )
   | _ => false,
   E ) > 0


fun is_dangerous E =
 exp_count(
   fn app_exp{ func, ... } => is_q func orelse 
        is_function func andalso (
        func = F orelse not( is_predefined_sym func ) )
   | _ => false,
   E ) > 0

 
fun dangerous_update E =
  if is_dangerous E then
    Dangerous := true
  else
    ()
 
(* Statistics gathering functions: *)

local
  val Simplify_count = ref 0
  val Eval_count = ref 0
in
  fun i X = if !X < Max_int then inc X else ()
  fun inc_simplify_count() = i Simplify_count
  fun inc_eval_count() = i Eval_count
  fun get_simplify_count() = !Simplify_count
  fun get_eval_count() = !Eval_count
end


local
fun pattern_match_subst'( 
      Pats : ('a,'b)e list, 
      Args : ('a,'b)e list
      ) : (symbol * ('a,'b)e) list option =
  case Args of
    nil => (case Pats of nil => SOME nil | _ => NONE)
  | Arg::nil => 
      if is_tuple_exp Arg then
        case Arg of app_exp{ args,... } =>
          pattern_match_subst'(Pats,args)
      else (
      case Pats of
        nil => NONE
      | _::_::_ => NONE
      | Pat::nil =>
      case Pat of
        app_exp{func,args=nil,...} => SOME( (func,Arg)::nil )
      | _ => NONE
      )
  | Arg1::Args1 =>
  case Pats of
    nil => NONE
  | Pat::nil => 
      if is_tuple_exp Pat then
        case Pat of app_exp{ args, ... } => 
          pattern_match_subst'(args,Args)
      else (
      case Pat of
        as_exp{var,pat,exp_info} => (
          case pattern_match_subst'(pat::nil,Args) of
            NONE => NONE
          | SOME Subst => SOME(
              (var,
               app_exp{func=TUPLE,args=Args,exp_info=exp_info})
              :: Subst )
          )
      | app_exp{func,args=nil,exp_info,...} => SOME(
          (func, app_exp{func=TUPLE,args=Args,exp_info=exp_info})
          :: nil )
      | _ => NONE
      )
  | Pat1::Pats1 =>
  case pattern_match_subst'(Pat1::nil,Arg1::nil) of
    NONE => NONE
  | SOME Subst1 =>
  case pattern_match_subst'(Pats1,Args1) of
    NONE => NONE
  | SOME Subst2 => SOME( Subst1@Subst2 )

in
fun pattern_match_subst(pat,args) = 
  pattern_match_subst'(pat::nil,args)
end (* local *)
      

structure H = Symbol_HashTable
        
exception Beta_expand
exception Return_NONE
fun beta_expand( 
      {func,pat,exp,...} : ('1a,'1b)d, 
      E : ('1a,'1b)e,
      Max_size : int ) : ('1a,'1b)e option =
let
  val Size_so_far = ref 0
  fun check_size_so_far() =
    if !Size_so_far > Max_size then
      raise Return_NONE
    else
      ()
  fun expand_call( Args : ('1a,'1b)e list ) : ('1a,'1b)e =
    case pattern_match_subst( pat, Args ) of
      NONE => raise Return_NONE
    | SOME Subst =>
    let
      val Table : ( ('1a,'1b)e * int ) H.hash_table =
        H.mkTable( 10, Beta_expand )
      val _ = map( fn(Par,Arg) =>
        H.insert Table ( Par, ( Arg, exp_size Arg ) ),
        Subst )
      fun instantiate( E as app_exp{ func, args=nil, ... } ) = (
            check_size_so_far();
            case H.find Table func of
              NONE => ( inc Size_so_far; E )
            | SOME( Arg, Arg_size ) => (
                Size_so_far := !Size_so_far + Arg_size;
                Arg ) )
        | instantiate( app_exp{ func, args, exp_info } ) = (
            inc Size_so_far;
            check_size_so_far();
            app_exp{
              func = func,
              args = map( instantiate, args ),
              exp_info = exp_info } )
        | instantiate( case_exp{ exp, rules, exp_info } ) = (
            inc Size_so_far;
            check_size_so_far();
            case_exp{
              exp = instantiate exp,
              rules = map( fn Rule as { pat, exp, ... } => 
               mk_rule( Rule, pat, instantiate exp ),
               rules ),
              exp_info = exp_info } )
         | instantiate( let_exp{ dec_list, exp, exp_info } ) = (
             inc Size_so_far;
             check_size_so_far();
             let_exp{
               dec_list = map( fn{ func, pat, exp, dec_info } =>
                 { func = func, pat = pat, 
                   exp = instantiate exp, dec_info = dec_info },
                 dec_list ),
               exp = instantiate exp,
               exp_info = exp_info } )
    in
      rename( instantiate exp, false )
    end (* fun expand_call *)

  val E_opt = SOME(
    exp_map( 
      fn Sub as app_exp{ func = F, args, ... } =>
        if F = func then (
          Size_so_far := 
            !Size_so_far - int_sum( map( exp_size, args ) );
          expand_call args )
        else (
          inc Size_so_far;
          check_size_so_far();
          Sub )
       | Sub => (
          inc Size_so_far;
          check_size_so_far();
          Sub ),
       E ) )
    handle Return_NONE => NONE

  in
    case E_opt of
      NONE => NONE
    | SOME E =>
    if !Size_so_far <= Max_size then
      SOME E
    else
      NONE

  end (* fun beta_expand *)
            

         
val Dangerous_beta_expanded = ref false
val Beta_expanded = ref false

fun dangerous_call_exists( G, Es ) : bool =
  exists( fn E =>
    exp_count(
      fn app_exp{ func, args, ... } =>
          if func = G then
            exists( is_dangerous, args )
          else
            false
       | _ => false,
       E ) > 0,
    Es )

fun simplify( 
      nil : ('1a,'1b)d list, 
      _ : ('1a,'1b)d list,
      exp : ('1a,'1b)e ) = (nil,exp)
  | simplify( D::Decs,Dec_list,exp) =
  let val (Decs,exp) = simplify(Decs,Dec_list,exp)
  in
    if not( sym_exp_member(#func D, exp) ) andalso
       forall( fn {func,exp,...} => 
         func = #func D orelse
         not( sym_exp_member(#func D, exp) ),
         Dec_list )
    then (
      Beta_expanded := true;
      ( Decs, exp )
      )
    else if exists(fn {exp,...} => 
         sym_exp_member(#func D,exp), 
         Dec_list )
    then
      ( D::Decs, exp )
    else 
    let
      val Max_size = exp_size( #exp D ) + exp_size exp
      val New_exp_opt = 
        beta_expand( not_act_to_dont_know_dec D, exp, Max_size )
    in
      case New_exp_opt of
        NONE => ( D::Decs, exp )
      | SOME New_exp => (
        Beta_expanded := true;
        Dangerous_beta_expanded := ( !Dangerous_beta_expanded orelse
          not( is_q_exp( #exp D ) ) andalso ( 
          contains_case_exp( #exp D ) orelse
          dangerous_call_exists( #func D, exp :: map( #exp, Decs ) ) ) );
        ( Decs, New_exp )
        )
    end
  end



exception Case_beta_expansion_exn
fun case_beta_expansion E =
(* Unfolding of constants defined by single rule case-expressions. *)
  let
    val Dangerous_case_beta_expanded = ref false
    val Table : int H.hash_table = H.mkTable( 2, Case_beta_expansion_exn )

    fun insert S =
      if not( is_variable S ) then
        ()
      else
        case H.find Table S of
          NONE => H.insert Table ( S, 1 )
        | SOME Multiplicity => H.insert Table ( S, Multiplicity + 1 )

    fun mult S = 
      case H.find Table S of
        NONE => 0
      | SOME N => N

    fun possible_expansion( Sub, E, V, Rhs ) =
      if mult V <= 1 orelse ( 
         not( contains_f_or_g E ) andalso
         1 + exp_size E + mult V >= exp_size E * mult V )
      then (
        Dangerous_case_beta_expanded := 
          ( !Dangerous_case_beta_expanded orelse
          contains_case_exp E orelse is_dangerous E );
        exp_map( 
          fn Sub as app_exp{ func, args = nil, ... } =>
               if func = V then rename( E, false ) else Sub
           | Sub => Sub,
           Rhs ) )
      else
        Sub
  in (
    exp_map( 
      fn Sub as app_exp{ func, args = nil, ... } => ( insert func; Sub )
       | Sub as case_exp{ exp, 
                  rules = Rules as [ { pat, exp = Rhs, ... } ], ... } => (
           case pat of
             app_exp{ func, args = nil, ... } =>
               if is_variable func then (
                 if length Rules >= 2 then
                   raise Case_beta_expansion_exn
                 else
                   ();
                 possible_expansion( Sub, exp, func, Rhs )
                 )
               else
                 Sub
           | as_exp{ var, pat, ... } =>
               if forall( fn V => mult V = 0, vars_in_pat pat ) then
                 possible_expansion( Sub, exp, var, Rhs )
               else
                 Sub
           | _ => Sub )
       | Sub => Sub,
       E ),
    !Dangerous_case_beta_expanded )
  end

fun add_not_activated_exps( E : ('a,'b)e ) : ('a,'b)e = 
  case E of
    app_exp{ func, args, exp_info } => app_exp{ func = func,
      args = map( add_not_activated_exps, args ),
      exp_info = exp_info }
  | case_exp{ exp, rules, exp_info } => case_exp {
      exp = add_not_activated_exps exp,
      rules = map( fn Rule as { pat, exp, activated, ... } =>
        let
          val exp = add_not_activated_exps exp
        in
          mk_rule( Rule, pat,
            if !activated then
              if is_not_activated_exp exp then
                gen_dont_know_exp( get_exp_info exp )
              else
                exp
            else if is_not_activated_exp exp then
              exp
            else
              gen_not_activated_exp( get_exp_info exp ) )
        end,
        rules ),
      exp_info = exp_info }
  | let_exp{ dec_list, exp, exp_info } => let_exp{
      dec_list = map( fn{ func, pat, exp, dec_info } =>
        { func = func, pat = pat, exp = add_not_activated_exps exp,
          dec_info = dec_info },
        dec_list ),
      exp = add_not_activated_exps exp,
      exp_info = exp_info }

val Add_not_activated_exps_timer = mk_timer "Add_not_activated_exps_timer"
fun add_not_activated_exps_time() =
  check_timer Add_not_activated_exps_timer

val add_not_activated_exps = fn X =>
  let
    val _ = start_timer Add_not_activated_exps_timer;
    val Y = add_not_activated_exps X
  in
    stop_timer Add_not_activated_exps_timer;
    Y
  end
    
      
fun vars_and_funcs E =
  exp_flat_map( 
    fn app_exp{ func, args,... } =>
        if null args then
          if is_variable func then [func] else []
        else
          [func]
    | _ => [],
    E )

val No_beta = ref false

fun redundant_case_removal(Es : ('1a,'1b)e list) 
    : ('1a,'1b)e list * symbol list =
(* Change case E of pat_1 => ?(V1) | ... | pat_i => E' | ... | pat_n => ?(Vn) 
   to E' if null(intersection(vars_in_pat pat_i,vars_in_exp E')), where E'
   is the only activated rhs of the case-exp.
*)
  case Es of
    nil => (nil,nil)
  | E::(Es as _::_) =>
  let 
    val (E::nil,Syms) = redundant_case_removal(E::nil)
    val (Es,Syms') = redundant_case_removal Es
  in
    (E::Es,Syms@Syms')
  end
  | E::nil =>
  case E of
    app_exp{func,args,exp_info} =>
      if null args then
        (E::nil,if is_variable func then func::nil else nil)
      else
        let val (args,Syms) = redundant_case_removal args
        in
          ( app_exp{func=func,args=args,exp_info=exp_info}::nil, 
            func :: Syms )
        end
  | case_exp{exp,rules,exp_info} =>
  let val (exp::nil,Syms) = redundant_case_removal(exp::nil)
  in
    case filter(fn{exp,...} => not(is_not_activated_exp exp),rules) of
      nil => ( 
        (gen_not_activated_exp(get_exp_info E)::nil,nil)
        )
    | { pat, exp=exp', ... } :: nil =>
    let 
      val (exp'::nil,Syms') = redundant_case_removal(exp'::nil)
    in
      if null(symbol_intersection(vars_in_pat pat,Syms')) then (
        dangerous_update exp;
        (exp'::nil,Syms')
        )
      else
        ( case_exp{exp=exp, rules=map(fn Rule as { pat, exp, ... } =>
            if is_not_activated_exp exp then
              Rule
            else
              mk_rule( Rule, pat, exp' ),
            rules ),
            exp_info=exp_info }::nil,
          Syms@Syms' )
    end
    | _ :: _ =>
    let val (Es,Syms') = redundant_case_removal(map(#exp,rules))
    in
      ( case_exp{exp=exp, rules = map( fn( exp, Rule as {pat,...} ) => 
          mk_rule( Rule, pat, exp ),
          combine(Es,rules) ),
          exp_info=exp_info }::nil,
        Syms@Syms' )
    end
  end
  | let_exp{ dec_list = [ D ], exp, exp_info } =>
  let 
    val ( [ E ], Syms ) = redundant_case_removal [ #exp D ]
    val D = 
      { func = #func D, pat = #pat D, exp = E, dec_info = #dec_info D }
    val ( [ exp ] , Syms' ) = redundant_case_removal [ exp ]


    fun ok( Func, Vars ) = !No_beta orelse
      length( symbol_intersection( Syms, Vars ) ) = length Vars andalso
      member( Func, Syms @ Syms' )


    val ( New_dec_list, New_exp ) =
      if ok( #func D, vars_in_pat( #pat D ) ) then
        ( [ D ], exp )
      else
        simplify( [ D ], [ D ], exp )
  in
    if null New_dec_list then
      ( [ New_exp ], vars_and_funcs New_exp )
    else
      ( [ let_exp{ dec_list = New_dec_list, exp = New_exp, 
          exp_info = exp_info } ],
        Syms' @ Syms )
  end

exception Remove_all_q_case_exps
fun remove_all_q_case_exps( E : ('a,'b)e ) : ('a,'b)e =
  exp_map( 
    fn Sub as case_exp{exp,rules,exp_info} =>
      if is_q_exp exp then
        if is_not_activated_exp exp then
          gen_not_activated_exp exp_info
        else if is_dont_know_exp exp then
          gen_dont_know_exp exp_info
        else
          raise Remove_all_q_case_exps
      else
        if forall(is_q_exp, map(#exp,rules)) then
          let val Ds = filter(is_dont_know_exp,map(#exp,rules))
          in
            if null Ds then #exp(hd rules) else hd Ds
          end
        else
          Sub
    | Sub as app_exp{ func, args, exp_info } => (
        if exists( is_q_exp, args ) then
          if forall( is_not_activated_exp, args ) then
            gen_not_activated_exp exp_info
          else 
            gen_dont_know_exp exp_info
        else
          Sub
         )
    | Sub => Sub,
    E)
   
val To_be_evaluated = ref false

exception Dead_code_elim_exn
fun dead_code_elim1( D as {func,pat,exp,dec_info} : ('1a,'1b)d ) 
    : ('1a,'1b)d =
  let 
    val _ = Beta_expanded := false
    val _ = Dangerous_beta_expanded := false
    val E = add_not_activated_exps(
      remove_all_q_case_exps(
        add_not_activated_exps( remove_all_q_case_exps exp ) 
        ) )
(* Note that remove_all_q_case_exps is used both before and after the
   call to add_not_activated_exps. The purpose of the first use is to
   remove app_exps that contain a q_exp.
*)
    val (exp::nil,_) = redundant_case_removal(E::nil)
    (* redundant_case_removal may change the semantics of the program. *)
    val ( exp, Dangerous_case_beta_expanded ) = 
      if !No_beta then ( exp, false ) else case_beta_expansion exp
    val exp = not_act_to_dont_know exp
  in
    if !No_beta andalso !Dangerous_beta_expanded then 
      raise Dead_code_elim_exn 
    else 
     ();
    let
      val New_D = { func = func, pat = pat, exp = exp, dec_info = dec_info }
    in
      if !Dangerous_beta_expanded orelse Dangerous_case_beta_expanded  then (
        To_be_evaluated := true;
        dead_code_elim1 New_D
        )
      else if !Beta_expanded then
        dead_code_elim1 New_D
      else
        New_D
    end
  end


fun dead_code_elim2( D : Ast.dec ) 
    : Ast.dec * Evaluate.program_eval_type option =
  let 
    val _ = To_be_evaluated := false
    val _ = Dangerous := false
    val New_D = dead_code_elim1 D
(*
    val  ( New_D, Eval_opt ) =
      if !To_be_evaluated orelse !Dangerous then 
        let 
          val () = type_check_dec_raise New_D
          val X = Evaluate.program_eval_fun New_D
        in
          inc_eval_count();
          case dead_code_elim2 New_D of
            ( New_D, NONE ) => ( New_D, SOME X )
          | ( New_D, SOME X ) => ( New_D, SOME X )
        end
      else
        ( New_D, NONE )
*)
  in
(*
    check( D, New_D, Eval_opt );
    ( New_D, Eval_opt )
*)
    ( New_D, NONE )
  end
    



(*
and check( D, New_D, Eval_opt ) =
      let
        open Evaluate
        val P = program_eval_fun D 
        val New_P = program_eval_fun New_D 
        val P = case Eval_opt of NONE => P | SOME P => P
      in
        if #n_c_n_w P <> #n_c_n_w New_P andalso
           #call_count New_P > #call_count P - 19998 then (
            output( !std_out, "\nWARNING: Different program eval values\n\n" );
            pre D;
            nl();
            pre New_D;
            output( !std_out, "\n\nBEFORE:\n");
            Print.print_dec' D;
            output( !std_out, "\n\nAFTER:\n");
            Print.print_dec' New_D
            )
        else
          ()
      end
*)

fun dead_code_elim( D : Ast.dec ) 
    : Ast.dec * Evaluate.program_eval_type option = (
  inc_simplify_count();
  dead_code_elim2 D
  )

fun dead_code_elim'( D  : ('1a,'1b)d ) : ('1a,'1b)d = (
  No_beta := true;
  Evaluate.program_eval_fun D;
  let 
    val New_D = dead_code_elim1 D
  in
    No_beta := false;
    New_D
  end
  )

(*
fun test() =
  let
    val D = mk_dec("int list -> int list",
"fun sort (Xs) = \
\  case Xs of \
\    nil => nil \
\  | X1::Xs1 => \
\      let fun g1(Ys) = \
\        case Ys of \
\          nil => X1::nil \
\        | X2::Xs2 => \
\        case X2<X1 of \
\          true => X2::g1(Xs2) \
\        | false => X1::Ys \
\      in \
\        case Xs of nil => nil | X3::Xs3 => g1(sort(Xs3)) \
\      end \
\" )
    val Act_cells_list = #act_cells_list(Evaluate.program_eval_fun D)
    val T = mk_timer "synt_lib.test"
  in
    start_timer T;
    map( fn _ => dead_code_elim( D, Act_cells_list),  fromto(1,1000) );
    case check_timer T of N => ( delete_timer T; N )
end
*)



fun remove_decs( E : ('1a,'1b)e ) : ('1a,'1b)e =
(* Remove a non-recursive g if the syntactic_complexity thereby is decreased.
   Remove let-exps with null(dec_list).
*)
  exp_map( fn let_exp{dec_list,exp,exp_info} =>
    let val (dec_list,exp) = simplify(dec_list,dec_list,exp)
    in
      if null dec_list then
        exp
      else
        let_exp{dec_list=dec_list,exp=exp,exp_info=exp_info}
    end
    | Sub => Sub,
    E )
  handle Ex => (
    output(!std_out,"\nremove_decs : E = \n");
    print_exp' E;
    re_raise(Ex,"remove_decs")
    )


fun remove_decs_in_dec({func,pat,exp,dec_info}:('1a,'1b)d) 
    : ('1a,'1b)d  * bool * bool = (
    Beta_expanded := false; 
    Dangerous_beta_expanded := false; 
    ( { func=func,
        pat=pat,
         exp=
           let
             val E = remove_decs exp
           in
             if is_not_activated_exp E then
               gen_dont_know_exp( get_exp_info E )
             else
               E
           end,
         dec_info=dec_info},
      !Beta_expanded,
      !Dangerous_beta_expanded
    ) )



fun beta_simplify_dec D =
  let 
    val Simplified = ref false
    fun g( D, Eval_opt ) =
      let
        val ( New_D, Beta_expanded, Dangerous_beta_expanded ) = 
          remove_decs_in_dec D
      in
        Simplified := ( !Simplified orelse Beta_expanded );
(*
        if Beta_expanded then
         let
           val Eval_opt =
             if Dangerous_beta_expanded then (
               inc_eval_count();
               SOME( Evaluate.program_eval_fun New_D )
               )
             else
               Eval_opt
          in
            case dead_code_elim2 New_D of
              ( New_D, NONE ) => g( New_D, Eval_opt )
            | ( New_D, SOME Eval_opt ) => g( New_D, SOME Eval_opt )
          end
        else
*)
          ( New_D, Eval_opt )
      end
    val ( New_D, Eval_opt ) = g( D, NONE )
  in
    if !Simplified then (
(*
       check( D, New_D, Eval_opt );
*)
       SOME( New_D, Eval_opt )
       )
    else
      NONE
  end




fun scope_check(E,Funcs,Pars) =
  is_q_exp E orelse
  case E of
    app_exp{func,args=nil,...} =>
      not(is_variable func) orelse member(func,Pars)
  | app_exp{func,args,...} => 
      ( func = TUPLE orelse func = SEMICOLON orelse
        Predefined.is_abstract_constructor func orelse
        member( func, map( #1, !Evaluate.Comps_to_use ) ) orelse 
        member( func, Funcs ) )
      andalso forall(fn Arg => scope_check(Arg,Funcs,Pars), args)
  | case_exp{exp,rules,...} =>
      scope_check(exp,Funcs,Pars) andalso
      forall( fn{ pat, exp, ... } => 
        scope_check( exp, Funcs, vars_in_pat pat@Pars ),
        rules )
  | let_exp{ dec_list, exp, ... } =>
  let val Funcs = map( #func, dec_list ) @ Funcs
  in
    scope_check(exp,Funcs,Pars) andalso
    forall( fn{pat,exp,...} => scope_check(exp,Funcs,vars_in_pat pat@Pars),
            dec_list )
  end

fun scope_check_dec( { func, pat, exp, ... } : ( 'a, 'b )d ) : bool =
  scope_check( exp, [ func ], vars_in_pat pat )


fun correctly_typed D =
let val Dec = remove_types_of_dec D
    val Ty_exp = 
      ty_con_exp( THIN_ARROW, 
        [ Predefined.input_type(), Predefined.output_type() ] )
  val Dec =
  Type.infer_types_of_dec_using_schema(
    Dec,
    {schematic_vars=vars_in_ty_exp Ty_exp, ty_exp=Ty_exp},
    Predefined.ty_env()
    )
in
  info_dec_eq( Dec, D )
end
handle _ => false


   


local

open Evaluate

in

fun simplify_loop( D ) =
  let
    val () = type_check_dec_raise D
    val Pe_D = program_eval_fun_max D
    val ( New_D, _ ) = dead_code_elim D
    val () = type_check_dec_raise New_D
  in
    if exp_eq( rename( #exp New_D, true ), rename( #exp D, true ) ) then
      D
    else 
    case quick_pe5_cmp( 
           program_eval_type_to_quick( program_eval_fun_max New_D ),
           program_eval_type_to_quick Pe_D )
    of
      EQUAL => (
(*
      output(!std_out,"\n");
      print_eval_value( mk_eval_value_max D );nl();
      print_dec' D;
      output( !std_out, "\n\nto \n" );
      print_eval_value( mk_eval_value_max New_D );nl();
      print_dec' New_D;
*)
      simplify_loop New_D
      )
    | _ => D
  end

end (* local *)

(* structure NN_opt = NN_opt_fn( Evaluate ) *)

end (* functor Synt_lib_functor *)
