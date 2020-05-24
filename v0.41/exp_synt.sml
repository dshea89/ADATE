(* File: exp_synt.sml.
   Created: 1993-06-10.
   Modified: 2000-04-03.

Synt of rconsts added 2000-04-03.
*)

signature EXP_SYNT =
sig

val synt_n : real * (int * real)list *
  bool *
  ( Ast.exp -> bool )option * 
  Ast.ty_exp * Ast.ty_env * (Ast.exp->Ast.exp) * Ast.dec * 
  Ast_lib.pos * Ast.symbol list * Ast.symbol list list * bool *
  (Ast.exp*real*Ast.symbol list -> unit) * real
  ->  unit
val no_of_exp_synt_evals : unit -> int
val cum_pure_exp_synt_time : unit -> real
val cum_exp_synt_time : unit -> real
val cum_small_exp_synt_time : unit -> real

val initialize : string -> unit

val equivalence_check : Ast.exp -> bool


structure Synt_lib : SYNT_LIB

end



functor Exp_synt_functor( Spec : SPEC ) : EXP_SYNT =
struct
open Lib List1 Ast Ast_lib Ast_lib6 Print Parse TGI

structure Synt_lib = Synt_lib_functor(structure Spec=Spec)
open Synt_lib Predefined

structure Evaluate = Synt_lib.Evaluate

val No_of_exp_synt_evals = ref 0
fun no_of_exp_synt_evals() = !No_of_exp_synt_evals

val Pure_exp_synt_timer = mk_timer "Pure_exp_synt_timer"
(* Expression synthesis time not including evaluation time. *)

(*
Expression Synthesis
--------------------

The empirical data indicates that simple, exhaustive and enumerative
expression synthesis may suffice. The synthesis algorithm does however
only synthesize expressions in which recursive calls satisfy the following
strict TGI-restriction (see [Dahl]):
Assume that f(A1,A2,...,An) is a recursive call and that f(X1,X2,...,Xn) is
the LHS of the def of f. At least one Ai must then be a "subexpression"
of Xi.

Example. Consider the def
fun f(Xs,Ys) =
  case Xs of 
    nil => ...
  | X1::Xs1 =>
  case Ys of 
    nil  => ...
  | Y1::Ys1 => E

When E is synted, the recursive calls f(Xs1,...) and f(...,Ys1) are allowed
but neither f(Xs,Xs) nor f(Xs,Xs1) are allowed.
The argument TGI_args of the function synt would for this example be
[ ( "f", [ (`Xs,[`Xs1]), (`Ys,[`Ys1]) ] ) ], where `Xs1 and `Ys1 are of type 
exp.
Since it isn't checked that all recursive calls contain a "subexpression"
in the same position, termination is actually not guaranteed.

In order to keep expression synthesis fast, it is assumed that each node in
the expression tree has a monomorphic type. A consequence of this is that
only predefined functions may be polymorphic. 
It is also assumed that each polymorphic predefined function either
has type 'a Ty_con or Ty_exp('a) -> 'a Ty_con where the only type variable
in Ty_exp('a) is 'a. This ensures that the Type argument to synt always is
monomorphic.
Example. Assume that the type of the exp to be synted, i.e. Type, is
int bin_tree and that bt_cons : 'a * 'a bin_tree * 'a bin_tree -> 'a bin_tree
is chosen as root. The domain type obviously becomes
int * int bin_tree * int bin_tree.


Synthesis of case-exps:

Synted exps contain 0, 1 or 2 cases at the "top level".
Assuming that N exps are synted, the distribution of exps w.r.t. no of case'es
is:   

No of cases  No of exps
0            N/3
1            N/3
2            N/3

Consider synting an exp of the form
case E of
  Pat1 => E1
| Pat2 => E2
...
| Patn => En.

The first step is to synt E. The pat's follow from the type of E. It is then
checked which rules that are activeted during execution if the exp Synt_site
in the current program is changed to
(case E of Pat1 => Activated(0):=true | Pat2 => Activated(2):=true...;
 Synt_site
 ), 
where each entry in the n-element boolean array Activated is initialized
to false. Assume that Activated_pats = [ Pat1',..,Patn' ] are the pats that
were activated. E is discarded if n'=1 and Pat1' doesn't contain any variable.
The entire exp synt is aborted if n'=0, since this means that the entire
case exp is unactivated.
The next step is to synthesize [ E1', ..., En' ] and construct the final synted
exp
case E of
  Pat1' => E1'
  ...
| Patn' => En'.


*)

(* Help functions: *)

(* Equivalence checking: *)

val Rejection_funs = ref( nil : (exp -> bool) list )

fun equivalence_check( E : exp ) =
  not(exists( fn F => F E, !Rejection_funs ))

fun add_id_left( app_exp{ func, args=app_exp{func=F,...}::_, ...} ) =
      func = PLUS andalso is_int F andalso int_sym_to_int F = 0
  | add_id_left _ = false

fun add_id_right( app_exp{ func, args= _::app_exp{func=F,...}::_, ...} ) =
      func = PLUS andalso is_int F andalso int_sym_to_int F = 0
  | add_id_right _ = false

fun add_assoc( app_exp{ func, 
        args = app_exp{ func=F, args=_::_::nil, ...}::_, ...} ) =
      func = PLUS andalso F = PLUS
  | add_assoc _ = false

fun addr_assoc( app_exp{ func, 
        args = app_exp{ func=F, args=_::_::nil, ...}::_, ...} ) =
      func = PLUSR andalso F = PLUSR
  | addr_assoc _ = false

fun add_comm( app_exp{ func, 
        args = [ A1 as app_exp{...}, A2 as app_exp{func = F2,...} ],
        ...} ) = 
      func = PLUS andalso F2 <> PLUS andalso app_exp_less(A1,A2) 
      (* Note: app_exp_less(A2,A1) doesn't work due to interaction with 
         assoc rejection. *)
  | add_comm _ = false

fun addr_comm( app_exp{ func, 
        args = [ A1 as app_exp{...}, A2 as app_exp{func = F2,...} ],
        ...} ) = 
      func = PLUSR andalso F2 <> PLUSR andalso app_exp_less(A1,A2) 
      (* Note: app_exp_less(A2,A1) doesn't work due to interaction with 
         assoc rejection. *)
  | addr_comm _ = false



fun mul_id_left( app_exp{ func, args=app_exp{func=F,...}::_, ...} ) = 
      func = MUL andalso is_int F andalso int_sym_to_int F = 1
  | mul_id_left _ = false

fun mul_id_right( app_exp{ func, args= _::app_exp{func=F,...}::_, ...} ) = 
      func = MUL andalso is_int F andalso int_sym_to_int F = 1
  | mul_id_right _ = false

fun mul_cancel_left( app_exp{ func, args=app_exp{func=F,...}::_, ...} ) =
      func = MUL andalso is_int F andalso int_sym_to_int F = 0
  | mul_cancel_left _ = false

fun mul_cancel_right( app_exp{ func, 
        args= _::app_exp{func=F,...}::_, ...} ) =
      func = MUL andalso is_int F andalso int_sym_to_int F = 0
  | mul_cancel_right _ = false

fun mul_assoc( app_exp{ func, 
        args= app_exp{ func=F, args=_::_::nil, ...}::_, ...} ) =
      func = MUL andalso F = MUL
  | mul_assoc _ = false

fun mul_comm( app_exp{ func, 
        args = [ A1 as app_exp{...}, A2 as app_exp{ func = F2, ...} ],
        ... } ) =
      func = MUL andalso F2 <> MUL andalso app_exp_less(A1,A2) 
      (* Note: app_exp_less(A2,A1) doesn't work due to interaction with 
         assoc rejection. *)
  | mul_comm _ = false


fun mulr_assoc( app_exp{ func, 
        args= app_exp{ func=F, args=_::_::nil, ...}::_, ...} ) =
      func = MULR andalso F = MULR
  | mulr_assoc _ = false

fun mulr_comm( app_exp{ func, 
        args = [ A1 as app_exp{...}, A2 as app_exp{ func = F2, ...} ],
        ... } ) =
      func = MULR andalso F2 <> MULR andalso app_exp_less(A1,A2) 
      (* Note: app_exp_less(A2,A1) doesn't work due to interaction with 
         assoc rejection. *)
  | mulr_comm _ = false

fun sub_id_right( app_exp{ func, args= _::app_exp{func=F,...}::_, ...} ) =
      func = MINUS andalso is_int F andalso int_sym_to_int F = 0
  | sub_id_right _ = false

fun div_id_right( app_exp{ func, args= _::app_exp{func=F,...}::_, ...} ) =
        func = DIV andalso is_int F andalso int_sym_to_int F = 1
  | div_id_right _ = false

fun div_zero( app_exp{ func, args= _::app_exp{func=F,...}::_, ...} ) =
      func = DIV andalso is_int F andalso int_sym_to_int F = 0
  | div_zero _ = false


fun eq_comm( app_exp{ func,
        args = [ A1 as app_exp{...}, A2 as app_exp{...} ],
        ... } ) =
      func = EQ andalso app_exp_less(A1,A2)
  | eq_comm _ = false

fun eq_refl( app_exp{ func, args=A1::A2::nil,...} ) = 
      func = EQ andalso exp_eq(A1,A2)
  | eq_refl _ = false


local

val NUMBER0 : symbol = int_to_symbol 0
val NUMBER1 : symbol = int_to_symbol 1

in

val Symbols_and_rejection_funs : 
    ( symbol list * ( ( 'a, 'b )e -> bool ) ) list = [
  ( [ PLUS, NUMBER0 ], add_id_left ),
  ( [ PLUS, NUMBER0 ], add_id_right ),
  ( [ PLUS ], add_assoc ),
  ( [ PLUS ], add_comm ),
  ( [ PLUSR ], addr_assoc ),
  ( [ PLUSR ], addr_comm ),
  ( [ MUL, NUMBER1 ], mul_id_left ),
  ( [ MUL, NUMBER1 ], mul_id_right ),
  ( [ MUL, NUMBER0 ], mul_cancel_left ),
  ( [ MUL, NUMBER0 ], mul_cancel_right ),
  ( [ MUL ], mul_assoc ),
  ( [ MUL ], mul_comm ),
  ( [ MULR ], mulr_assoc ),
  ( [ MULR ], mulr_comm ),
  ( [ MINUS, NUMBER0 ], sub_id_right ),
  ( [ DIV, NUMBER1 ], div_id_right ),
  ( [ DIV, NUMBER0 ], div_zero ),
  ( [ EQ ], eq_comm ),
  ( [ EQ ], eq_refl )
  ]

end (* local *)

val Exp_synt_initialized = ref false

fun initialize Spec_file = (
  Synt_lib.initialize Spec_file;
  Rejection_funs :=
    Spec.Reject_funs @
    let val Comp_syms = map(#1,Predefined.ty_env())
    in
      map( #2, filter( fn(Syms,_) => is_subset(Syms,Comp_syms),
                 Symbols_and_rejection_funs ) )
    end;
    Exp_synt_initialized := true;
    p"\nNumber of rejection func = "; print_int( length( !Rejection_funs ) ) )






(* S_min checking 
   -----------------

For each combination of Type and Min_once values, the min size S_min of
a synted app_exp, that contains components as specified by Min_once,
is stored.

S_min_store = [ ( Type, [ (Min_once,S_min), (Min_once,S_min),... ] ), ... ]

When synt'(Type,S_max,Components,Min_once,TGI_args,emit) never calls emit,
the S_min value for all Type' and Min_once' values, s.t. Min_once is a 
subset of Min_once', is set to max( Old S_min, S_max+1 ).
*)

type min_once_type = symbol list list

type data = {
  rconst_values : real list,
  no_rconst_synt : bool,
  dupl_case_synt : bool, (* true iff case-tree for the DUPL transformation
    is to be made. *)
  tgi_required : bool ref,
  eq_check_activated : bool,
  s_min_store : (ty_exp * (min_once_type*int) list) list ref,
  activated : bool ref }

local
  fun  update_Min_s_list(Min_once,S_max,Min_s_list : (min_once_type*int) list) =
    let
      val Min_s_list = map( fn X as (Min_once',S_min') =>
        if is_subset(Min_once,Min_once') then
          ( Min_once', max2(op<,S_min',S_max+1) )
        else
          X,
        Min_s_list )
    in
      case assoc_opt(Min_once,Min_s_list) of
        SOME _ =>  Min_s_list
      | NONE =>
      let val (_,Max_s) = max( fn((_,S1),(_,S2)) => S1<S2,
        (nil,S_max+1) ::
        filter( fn(Min_once',_) => is_subset(Min_once',Min_once), Min_s_list )
        )
      in
        (Min_once,Max_s)::Min_s_list 
      end
    end

  fun update_s_min_store( Type, Min_once, S_max, S_min_store ) =
    case S_min_store of
      nil => ( Type, (Min_once,S_max+1)::nil ) :: nil
   | (X as (Type',Min_s_list)) :: Xs =>
   if Type<>Type' then
     X::update_s_min_store(Type,Min_once,S_max,Xs)
   else
     (Type',update_Min_s_list(Min_once,S_max,Min_s_list))::Xs
  
in (* local *)

fun new_data( Rconst_values, No_rconst_synt,DUPL, Eq_check ) : data = 
  { rconst_values = Rconst_values,
    no_rconst_synt = No_rconst_synt,
    dupl_case_synt = DUPL,
    tgi_required = ref false,
    eq_check_activated = Eq_check, 
    s_min_store = ref nil, activated = ref false }

fun  update_s_min( Data : data, Type, Min_once, S_max ) = 
  if !( #activated Data ) then
    ( #s_min_store Data ) := 
      update_s_min_store( Type, Min_once, S_max, !( #s_min_store Data ) )
  else
    ()

fun lookup_s_min( Data : data, Type, Min_once ) : int =
  if not( !( #activated Data ) ) then 1 else
  let fun u() = (
    ( #s_min_store Data ) := 
      update_s_min_store( Type, Min_once, 0, !( #s_min_store Data ) );
    lookup_s_min( Data, Type, Min_once )
    )
  in
    case assoc_opt( Type, !( #s_min_store Data ) ) of
      NONE => u()
    | SOME Min_s_list =>
    case assoc_opt(Min_once,Min_s_list) of
      NONE => u()
    | SOME S_min => S_min
  end

end (* local *)

fun partition_min_once Min_once =
  if null Min_once then
    [ ([],[]) ]
  else
  let val Powset = powset(Min_once,nil) 
    val Part =
      flat_map( fn(X,Y) => (X,Y)::(Y,X)::nil,
        map( fn Set => (Set,difference(Min_once,Set)), 
             take(length(Powset) div 2,Powset) )
        )
  in
    sort (fn((Xs1,_),(Xs2,_)) => length Xs1>length Xs2) Part
  end
  

fun min_size_types( Data : data, Types, Min_once ) =
  case Types of
    T1::nil => lookup_s_min( Data, T1, Min_once )
  | T1::Ts1 =>
      min( op<,
        map( fn( Now, Later ) =>
          lookup_s_min( Data, T1, Now ) + min_size_types( Data, Ts1, Later ),
          partition_min_once Min_once )
        ) 





val Exp_synt_timer = mk_timer "Exp_synt_timer"
val Small_exp_synt_timer = mk_timer "Small_exp_synt_timer"



(*
fun test(Dec,Ty_exp) = 
  construct_case_exp( 
    Parse.parse_ty_exp"hgeff", 
    Type.parse_exp_t(Dec,Ty_exp)
    )
*)

fun activation_check( Renamed_prog : dec, Pos : pos, So_far : exp,
      P : pos ) : bool list =
  let 
    val D = pos_replace_dec(Renamed_prog,Pos,fn Sub =>
              app_exp{func=SEMICOLON,args=So_far::Sub::nil,
                exp_info=get_exp_info Sub} )
    val _ = stop_timer Pure_exp_synt_timer
    val _ = inc No_of_exp_synt_evals
    val () = type_check_dec_raise D
    val _ = Evaluate.program_eval_fun D
    val E = add_not_activated_exps( #exp D )
    val _ = start_timer Pure_exp_synt_timer
  in 
    if not( is_legal_pos( Pos@(0::P), E ) ) then nil else
    case pos_to_sub( E, Pos@(0::P) ) of
      case_exp{rules,...} =>
        map( fn{ exp, ... } => not(is_not_activated_exp exp), rules )
    | _ => nil
  end
  handle Ex => (
    flush_out( !std_out );
    output(!std_out,"\nRenamed_prog =\n");
    print_dec' Renamed_prog;
    output(!std_out,"\nPos =\n");
    print_int_list Pos;
    output(!std_out,"\nSo_far =\n");
    print_exp' So_far;
    output(!std_out,"\nP =\n");
    print_int_list P;
    re_raise(Ex,"Activation_check")
    )


fun dupl_activation_check( Renamed_prog : dec, Pos : pos, So_far : exp,
      P : pos, Old_eval : Evaluate.eval_value_type  ) : bool list =
let 
  val RHS_poses = 
    Ast_lib2.selected_rhs_poses So_far @ Ast_lib2.other_rhs_poses So_far
  val RHS = pos_to_sub( #exp Renamed_prog, Pos )

  val D = pos_replace_dec( Renamed_prog, Pos, fn _ => 
    poses_replace( So_far, RHS_poses, fn _ => rename( RHS, false ) ) )

  val _ = stop_timer Pure_exp_synt_timer
  val _ = inc No_of_exp_synt_evals
  val () = type_check_dec_raise D
  val Eval = Evaluate.mk_eval_value D
  val E = add_not_activated_exps( #exp D )
  val _ = start_timer Pure_exp_synt_timer
in 
  if not( Evaluate.better_or_equal( Eval, Old_eval ) ) then [] else
  if not( is_legal_pos( Pos@P, E ) ) then nil else
  case pos_to_sub( E, Pos@P ) of
      case_exp{rules,...} =>
        map( fn{ exp, ... } => not(is_not_activated_exp exp), rules )
    | _ => nil
  end
  handle Ex => (
    flush_out( !std_out );
    output(!std_out,"\nRenamed_prog =\n");
    print_dec' Renamed_prog;
    output(!std_out,"\nPos =\n");
    print_int_list Pos;
    output(!std_out,"\nSo_far =\n");
    print_exp' So_far;
    output(!std_out,"\nP =\n");
    print_int_list P;
    re_raise(Ex,"Dupl_activation_check")
    )




fun construct_checked_case_exp(Type, O : int list * ty_env, E, Pats, 
        Act_pats ) : exp * (int list * ty_env) list =
let
fun construct_rules( _, _, nil, nil ) = (nil,nil)
  | construct_rules( O as (Pos,Delta_comps), Rule_no, Pat::Pats, Act::Acts ) =
  let val (Rules,Pos_comps) = construct_rules(O,Rule_no+1,Pats,Acts)
  in
  if Act then
    ( mk_new_rule( Pat, Predefined.proper_dummy_exp Type ) :: Rules, 
      ( snoc(Pos,Rule_no), comps_in_pat Pat @ Delta_comps ) :: Pos_comps
      )
  else
    ( mk_new_rule( Pat, gen_not_activated_exp Type ) :: Rules, Pos_comps )
  end

  val (Rules,Pos_comps) = construct_rules(O,1,Pats,Act_pats)
  in
    ( case_exp{exp=E, rules=Rules, exp_info=Type}, Pos_comps )
  end

structure H = Lib.Real_HashTable

fun case_synt( Data : data, S_max : int, Total_n_cases : int, 
    TGI_args : TGI.TGI_args_type, 
    Act_check_memo_table : bool list H.hash_table,
    Case_analyzed_exps, Type : ty_exp, 
    Components : ty_env, Min_once : symbol list list, Subst_fun : exp->exp, 
    Renamed_prog : dec, Old_eval : Evaluate.eval_value_type, 
    dupl_analyzed_exp_ok : ( exp -> bool )option,
    Pos : int list, 
    Max_once : symbol list, emit : exp*int -> unit, continue : unit -> bool ) =
(* Calls emit(E1,S1), emit(E2,S2),... emit(En,Sn), where E1,E2,... En 
   are synted exps, while continue() = true. Si is the size of Ei.
   E1,..., En are all exps of size <= S_max.
   A component that occurs in Max_once may not occur more than once in a
   synted exp.
*)
  
let 
  fun non_tgi_backtrack Non_tgi_present =
    Non_tgi_present andalso !(#tgi_required Data)
  exception Synt
  val DUPL = #dupl_case_synt Data
  val Dont_know_exp_type = Type
  val _ = 
    if Total_n_cases = 0 then 
      ( #activated Data ) := true
    else (
      if not(null Min_once) then raise Synt else ();
      ( #activated Data ) := false
      )

fun synt'(Non_tgi_present : bool, Not_constructor : bool, Type : ty_exp, 
      Immediately_prohibited : symbol list,
      S_max : int, 
      Components : ty_env, Min_once, 
      Prohibited : symbol list, TGI_args : TGI.TGI_args_type, 
      emit : exp*int*ty_env * bool -> unit ) =
if S_max<=0 orelse S_max < lookup_s_min( Data, Type, Min_once ) orelse 
   non_tgi_backtrack Non_tgi_present orelse not(continue()) then
  ()
else 
  let
    val Emitted = ref false
    fun emit' X = (Emitted := true; emit X )
  in
  case Type of
    ty_con_exp(Ty_con,Args) => 
      if Ty_con<>TUPLE_TY_CON then () else
      if Not_constructor then () else
      synt_list( Non_tgi_present, Args, map( fn _ => [], Args ), 
        S_max-1, Components, Min_once, Prohibited, TGI_args,
        fn (Es,S,Comps, Present) => emit'(app_exp{ func=TUPLE, args=Es, 
                               exp_info=Type },
                          S+1, Comps, Present orelse Non_tgi_present )
        )
  | _ => ();

  if Rconst.is_rconst_type Type andalso null Min_once then
    if #no_rconst_synt Data then
      case randReal() * rand_choice( #rconst_values Data ) of RC =>
      emit'( mk_rconst_exp( 0, 0.1, RC ), 1, Components, 
        Non_tgi_present )
    else
      Rconst.synt_rconst( S_max, Components, Max_once,
        fn( E, S, Comps ) => emit'( E, S, Comps, Non_tgi_present ),
        continue  )
  else
  while_list(
    continue,
    Components,
    fn (F,{schematic_vars,ty_exp}) =>
    if Not_constructor andalso is_constructor F then () else 
    if member(F,Prohibited) orelse member( F, Immediately_prohibited ) then 
      () 
    else
    let 
      val New_components =
        if member(F,Max_once) then
          filter( fn(F',_) => F<>F', Components )
        else
          Components
      val New_min_once = filter( fn Xs => not(member(F,Xs)), Min_once )
    in
    if is_fun_type ty_exp then
      case ty_exp of ty_con_exp( _, Domain'::Range::nil ) => (
          case match(Range,Type) of
            NONE => ()
          | SOME Subst_fun => (
          case assoc_opt(F,TGI_args) of
SOME Par_subs_list => 
  let 
    val Argss = map(#2,Par_subs_list)
    val Argss_syms = map( fn Args =>
      map( fn app_exp{ func, args=[], ... } => func, Args ),
      Argss )
    val Ds = mk_ty_exp_list(Subst_fun Domain')
    val Arity = length Argss
    val _ = if Arity<>length(Ds) then raise Synt else ()

    fun emit_tgi_choice( Choice : exp option list ) : unit =
    let
      val N_chosen = int_sum( map( fn NONE => 0 | SOME _ => 1, Choice ) )
      val Delta_s = if N_chosen = 0 then 1 else N_chosen
      val Non_tgi_present = Non_tgi_present orelse N_chosen = 0
    in
      if N_chosen = 0 andalso !( #tgi_required Data) then () else
      synt_list( Non_tgi_present,
        remove_somed( Ds, Choice ), 
        remove_somed( Argss_syms, Choice ),
        S_max-Delta_s, New_components, New_min_once, 
        if !( #tgi_required Data ) then F::Prohibited else Prohibited, 
        TGI_args,
        fn( Es, S, Comps, Present ) => 
          emit'(
            app_exp{ func = F, args = add_somed( Es, Choice ), 
                     exp_info = Type },
            S + Delta_s, 
            Comps, Present orelse Non_tgi_present ) )
    end
  in
    make_tgi_choices( Argss, emit_tgi_choice )
  end

| NONE =>
      synt'(Non_tgi_present, false, 
        Subst_fun Domain', [], S_max-1, New_components, New_min_once, 
        Prohibited,  TGI_args,
        fn (E,S,Comps, Present) => 
        let 
          val Es = mk_exp_list E
          val To_emit = app_exp{ func=F, args=Es, exp_info=Type }
        in
          if not( #eq_check_activated Data ) orelse 
             equivalence_check To_emit 
          then
            emit'(To_emit,S+1,Comps, Present orelse Non_tgi_present)
          else
            ()
        end
        )
    ) (* case assoc_opt(...) *)
    ) (* case match(...) *)
     
    else (* if is_fun_type ty_exp *)
      case New_min_once of _::_ => () 
      | nil =>
      case match(ty_exp,Type) of
        NONE => ()
      | SOME _ => 
          emit'(app_exp{ func=F, args=nil, exp_info=Type },
               1,New_components, Non_tgi_present) 
    end (* val New_components *)
    ); (* while_list *)
  if !Emitted then
    ()
  else
    update_s_min( Data, Type, Min_once, S_max)
  end (* synt' *)

and synt_list( Non_tgi_present : bool,
      Types, Disallowed_tgi_argss, S_max, Components, 
      Min_once, Prohibited, TGI_args, emit) =
  if S_max < 0 orelse non_tgi_backtrack Non_tgi_present orelse
     not(continue()) then 
(* This if-test is only an optimization to prevent an unnecessary but harmless 
   call to synt. *)
    ()
  else
  case ( Types, Disallowed_tgi_argss ) of
    ( nil, nil ) => 
      ( case Min_once of _::_ => () 
        | nil => emit(nil,0,Components, Non_tgi_present ) ) 
  | ( [ T1 ], [ Args ] ) =>
      synt'(Non_tgi_present, false, T1, Args, S_max,Components,
        Min_once,Prohibited,TGI_args,
        fn(E,S,Comps, Present) => 
          emit(E::nil,S,Comps, Present orelse Non_tgi_present) )
  | ( T1 :: Ts1, Args :: Argss ) => 
      loop( fn(Now,Later) => (* The union of Now and Later is Min_once. *)
        synt'(Non_tgi_present, false, T1, Args, 
          S_max-min_size_types( Data, Ts1, Later ), 
          Components, Now, 
          flatten Later @ Prohibited, TGI_args,
          fn (E,S,Comps, Present) => 
            synt_list( Present orelse Non_tgi_present, Ts1, Argss, 
              S_max-S, Comps, 
              Later, Prohibited, TGI_args,
              fn(Es,S',Comps', Present) => 
                emit(E::Es,S+S',Comps', Present orelse Non_tgi_present) )
          ),
        partition_min_once Min_once )


fun pats_ok( Pats : ( 'a, 'b )e list, Activated_pats : bool list ) = 
(* Example. case E of true => Rhs1 | false => Rhs2 is allowed only if
   Activated_pats=[true,true]. In general, if only one pattern is activated, 
   this pattern must contain at least one variable.
*)
  if length Pats <> length Activated_pats then false else
  let 
    val Active_pats = map( #1, filter( #2, combine( Pats, Activated_pats )))
  in
    case Active_pats of
      nil => false
    | Pat::nil => not DUPL andalso not(null (vars_in_pat Pat)) 
    | _ => true
  end
  handle Ex => (
    p"\n\npats_ok:\n";
    loop( fn E => ( Print.print_exp' E; p" : " ), Pats ); nl();
    loop( fn X => p( Bool.toString X ), Activated_pats ); nl();
    re_raise( Ex, "pats_ok" ) )


fun case_synt_lower( Non_tgi_present, S_max, Components, So_far, So_far_size,
    Pos_comps : (int list * ty_env) list ) =
  case Pos_comps of
    nil => emit(So_far,So_far_size)
  | (Pos,Delta_comps) ::  Pos_comps1 => (
  case_synt_lower( Non_tgi_present, S_max-1, Components, 
    pos_replace(So_far,Pos, fn _ => gen_dont_know_exp Dont_know_exp_type ), 
    So_far_size+1, Pos_comps1 );
  synt'(Non_tgi_present, false, Type, [], S_max-length(Pos_comps1), 
    Components@Delta_comps, Min_once, nil,
    TGI.fill_in_tgi_args(So_far,TGI_args,Pos),
    fn(Rhs,S,Comps, Present) =>
      case_synt_lower( Present orelse Non_tgi_present, S_max-S, 
        take( length Comps-length Delta_comps, Comps ),
        pos_replace(So_far,Pos, fn _ => Rhs), So_far_size+S, Pos_comps1 )
    )
  )


fun case_synt_upper( Non_tgi_present : bool, N_cases : int, S_max : int, 
    Components : ty_env,
    So_far : exp, So_far_size : int, 
    Open as (O as (P,Delta_comps))::Os : (int list * ty_env) list,
    Closed : (int list * ty_env) list ) =
  if 
    if DUPL then
      S_max < 0 orelse not( continue() ) orelse 
      non_tgi_backtrack Non_tgi_present orelse
      not( Exp_synt_lib2.analyzed_order_ok So_far )
    else
      S_max < N_cases*2+length(Open)+length(Closed) orelse 
      non_tgi_backtrack Non_tgi_present orelse not(continue()) 
  then
    ()
  else if N_cases=0 then
    case_synt_lower( Non_tgi_present, S_max,Components,So_far,
      So_far_size,Open@Closed)
  else (
  if DUPL andalso null Os then emit( So_far, So_far_size ) else ();

  (* Don't choose P. *)
  if not(null Os) then
    case_synt_upper( Non_tgi_present, N_cases,S_max,Components,
      So_far,So_far_size,Os,O::Closed)
  else
    ();
  (* Choose P. Synt a case-exp and insert it at position P. Then do
     activation checking. Insert the revised case-exp at position P.
  *)
  let val Possible_E_types = 
      make_set(flat_map( fn( _, {schematic_vars,ty_exp} ) =>
        if null(vars_in_ty_exp ty_exp) then
          range_type ty_exp :: nil
        else 
          nil,
        Components
        ))
  fun emit_E(E',S,Comps, Present) =
    case Subst_fun E' of 
  E as app_exp{func,args, exp_info=ty_con_exp(Constr,Args) } =>
    if is_constructor func then () else   
    if null args andalso Constr<>TUPLE_TY_CON andalso 
       ( not(is_in_Ddec_table Constr) orelse is_abstract_type Constr ) then
      ()
    else if member'( exp_eq, E, Case_analyzed_exps ) orelse
         member'( exp_eq, E, case_analyzed_exps_at_pos(So_far,P) ) orelse
         DUPL andalso not( (case dupl_analyzed_exp_ok of SOME X => X) E ) 
    then
      ()
    else
      let 
        val Case_E' as case_exp{rules,...} = construct_case_exp(Type,E')
        val Pats = map(fn{pat,...}=>pat,rules)
        val Finger_print = exp_hash E'
        fun compute() = 
          if DUPL then
            dupl_activation_check( Renamed_prog, Pos,
              Subst_fun( pos_replace(So_far,P,fn _ => Case_E' )), P, Old_eval )
          else
            activation_check(Renamed_prog,Pos,
              Subst_fun( pos_replace(So_far,P,fn _ => Case_E' )), P)
        val Act_pats = 
          if N_cases = Total_n_cases then
            case H.find Act_check_memo_table Finger_print of
              NONE => let val Act_pats = compute() in
                if H.numItems Act_check_memo_table < 
                   Constants.Total_max_REQ_storage 
                then
                  H.insert Act_check_memo_table (Finger_print,Act_pats)
                else
                  ();
                Act_pats
                end
            | SOME Act_pats => Act_pats
          else
            case H.find Act_check_memo_table Finger_print of
              NONE => compute()
            | SOME Act_pats' =>
                if null Act_pats' orelse not( pats_ok( Pats, Act_pats' ) ) then
                  []
                else
                  compute()
      in
      if null Act_pats orelse not(pats_ok(Pats,Act_pats)) then
        ()
      else
      let val (Checked_Case_E,Add_open) =
        construct_checked_case_exp(Type, O, E', Pats, Act_pats )
      in
        case_synt_upper( Present orelse Non_tgi_present,
          N_cases-1, S_max-S-1, drop(length Delta_comps, Comps),
          pos_replace(So_far,P, fn _ => Checked_Case_E), 
          So_far_size+S+1, 
          if DUPL then Add_open else Add_open@Os, 
          Closed )
      end
      end 
  | _ => ()
  in
    loop( fn E_type => 
      synt'(Non_tgi_present, true, E_type, [], 
        if DUPL then S_max-1 else S_max-N_cases*2+1-length(Open)-length(Closed),
        Delta_comps@Components, Min_once, nil, TGI.fill_in_tgi_args(So_far,
        TGI_args,P),
        emit_E),
      Possible_E_types )
  end (* Choose P. *)
  )

in 
  case_synt_upper( false, Total_n_cases, S_max, Components, 
    Predefined.proper_dummy_exp Type, 0, [([],[])], [] )
end (* case_synt *)
handle Ex => re_raise(Ex,"Case_synt")

fun print_max_once( Max_once : symbol list ) : unit =
  print_list( fn Sym => output(!std_out,symbol_to_string Sym), Max_once )

fun print_min_once( Min_once : symbol list list ) : unit =
  print_list( fn Syms => 
    print_list( fn Sym => output(!std_out,symbol_to_string Sym), Syms ),
    Min_once )

exception Min_once_check
fun min_once_check( Min_once : symbol list list, Synted_exp : exp ) : bool =
(* Example. Min_once = [ [s1], [s1,s2] ] means that s1 must be used at least 
   once in Synted_exp and that s2 or s3 also must be used at least once in
   Synted_exp.
*)
  let fun new_min_once(Min_once,E) =
    let val Syms_in_exp = symbols_in_app_exp E
    handle Match => (
      output(!std_out,"\n\nMin_once = ");
      print_min_once Min_once;
      output(!std_out,"\n\nSynted_exp = "); print_exp' Synted_exp;
      output(!std_out,"\n\nE = "); print_exp' E;
      raise Min_once_check
      )
    in
      filter( fn Sym_list => null(symbol_intersection(Sym_list,Syms_in_exp)),
              Min_once )
    end

  fun cse(Min_once,E) : symbol list list =
    case E of
      case_exp{exp,rules,...} =>
        let val New_min_once = new_min_once(Min_once,exp)
          val Active_rules = 
            filter( fn{ exp, ... } => not( is_not_activated_exp exp ),
              rules)
        in
          case Active_rules of
            { pat, exp, ...} :: nil => 
              cse( vars_in_pat pat :: New_min_once, exp )
          | _::_::_ =>
            let 
              fun check_rules( Min_once, 
                      nil : (exp_info_type,dec_info_type)rule_type list ) = 
                    Min_once
                | check_rules( Min_once, {exp,...}::Rules ) =
              check_rules( cse(Min_once,exp), Rules )
            in
              check_rules(New_min_once,Active_rules)
            end
        end (* val New_min_once *)
    | app_exp{...} => new_min_once(Min_once,E)
  in
    null( cse(Min_once,Synted_exp) )
  end (* fun min_once_check *)

  
local
  fun eq_list nil = true
    | eq_list( X::nil) = true
    | eq_list( X1::X2::Xs ) = X1=X2 andalso eq_list(X2::Xs)
in
  fun equal_rhs_check( Synted_exp ) : bool =
    case Synted_exp of
      case_exp{rules,...} =>
        let val Rhses = map(#exp,rules) in
          forall(equal_rhs_check,Rhses) andalso
          ( case Rhses of _::nil => true | _ => not( eq_list Rhses ) )
        end
    | _ => true
end

fun print_synt_n_args( Type : ty_exp, Components : ty_env,
    Current_prog : dec, Pos : pos, Max_once : symbol list, 
    Min_once : symbol list list, Eq_check : bool, N_exps : real ) = 
let
  fun p S = output( !std_out, S )
in
  p "\nType = "; print_ty_exp Type;
  p "\nComponents = \n"; print_ty_env Components;
  p "\n\nCurrent_prog = \n"; print_dec' Current_prog;
  p "\n\nPos = \n"; print_int_list Pos;
  p "\n\nMax_once = \n"; print_max_once Max_once;
  p "\n\nMin_once = \n"; print_min_once Min_once;
  p( "\n\nEq_check = " ^ Bool.toString Eq_check );
  p( "\nN_exps = " ^ Real.toString N_exps )
end

exception No_of_cases_distribution_exn
exception Act_check_memo_table_exn
fun synt_n( 
    Synt_and_eval_time_per_exp : real, 
    (* Given as parameter to minimize differences between first and second run
       for DUPL in particular but also for REQ and MULTIR. *)
    No_of_cases_distribution : ( int * real )list,
    NN_post_opt : bool,
    DUPL_mode : ( exp -> bool )option,
    Type : ty_exp, Components : ty_env, Subst_fun : exp->exp, 
    Current_prog : dec, Pos : pos, Max_once : symbol list, 
    Min_once : symbol list list, Eq_check : bool,
    emit : exp*real*symbol list->unit, 
    N_exps : real ) =
  let
    val true = !Exp_synt_initialized
    val false = NN_post_opt
    val () = 
      if real_eq( real_sum( map( #2, No_of_cases_distribution ) ), 1.0 ) then
        ()
      else
        raise No_of_cases_distribution_exn
(*
    val () = ( p"\nsynt_n started. N_exps = "; print_real N_exps;
               flush_out( !std_out ) )
*)
    val emit = fn X as ( E, Cost, _ ) => emit X
      handle Ex => (
        p"\n\nemit in synt_n:\n\n";
        Print.print_exp' E;
        p( "\n\n" ^ Real.toString Cost ^ "\n\n" );
        re_raise( Ex, "emit in synt_n" ) )
    val Emitted_count = ref 0.0
    val _ = start_timer Pure_exp_synt_timer
    val _ = start_timer Exp_synt_timer
    val _ = if N_exps<10.0 then start_timer Small_exp_synt_timer else ()
    val Act_check_memo_table : bool list H.hash_table =
      H.mkTable(10,Act_check_memo_table_exn)
    val Max_size = 10 + floor(Math.ln(N_exps+1.0)/Math.ln 1.2)
    fun is_let_val( case_exp{ rules, ... } ) =
      case rules of
        [ _ ] => true
      | _ :: _ => false
    val Is_case_exp_pos =
      not(null Pos) andalso dh Pos = 0 andalso
      let
        val Sub = pos_to_sub( #exp Current_prog, lt Pos )
      in
        is_case_exp Sub andalso not( is_let_val Sub )
      end

    val Rconst_values = if not NN_post_opt then [] else
      take( 100, scramble( map( rconst_exp_to_real,
        exp_filter( Rconst.is_rconst_exp, #exp Current_prog ) ) ) )
       
    val Case_analyzed_exps = 
      case_analyzed_exps(#pat Current_prog) @
      case_analyzed_exps_at_pos(#exp Current_prog,Pos) @
      flat_map( fn(F,{schematic_vars,ty_exp}) =>
        if null schematic_vars then
          if is_fun_type ty_exp then
            nil
          else
            case_analyzed_exps( Subst_fun(
              app_exp{func=F,args=nil,exp_info=ty_exp} ))
        else
          nil,
        Components )
    val TGI_args = TGI.tgi_args(Current_prog,Pos)
    val DUPL = is_SOME DUPL_mode
    val Data = new_data( Rconst_values, NN_post_opt, DUPL, Eq_check )
    val case_synt = 
      let 
        val {func,pat,exp,dec_info} = Current_prog
        val Renamed = {func=func, pat=pat, 
            exp=pos_replace(exp, Pos, fn Sub => rename(Sub,false)),
            dec_info=dec_info}
        val Old_eval = Evaluate.mk_eval_value Renamed
      in
        fn(S_max,N_cases,emit,continue) =>
          case_synt( Data, S_max,N_cases,TGI_args,Act_check_memo_table,
            Case_analyzed_exps, Type,Components,
            if N_cases=0 then Min_once else nil,
            Subst_fun, Renamed, Old_eval, DUPL_mode,
            Pos, Max_once, emit, continue )
      end
    val case_synt = fn(N_cases,emit,continue) =>
      let
        fun produce S =
          if S>Max_size orelse not( continue() ) then () else
          let  fun emit'(E',S') = if S=S' then emit(E',S') else ()
          in
        (*    p"\n\nproduce: S = "; print_int S; nl();nl(); *)
            case_synt( S, N_cases, emit', continue );
            produce( S+1 )
          end
      in
        produce 1
      end
    val Base_cum_eval_time = Evaluate.cum_eval_time()
    val case_synt = fn(N_cases,emit:exp*symbol list->unit,N:real) =>
      if N<3.0 then N else
      let
        val Buffer : (exp*symbol list) list ref = ref nil
        val N_Buffer = ref 0
        val So_far = ref 0.0
        val Time_limit = max2( op<, N*1.0*Synt_and_eval_time_per_exp,
                           9.0*Synt_and_eval_time_per_exp )
        val Timer = mk_timer "synt_n"
        val _ = start_timer Timer
        fun continue() = (
          if !So_far > Constants.Free_exp_synt_share * N orelse
             check_timer Timer > Constants.Free_exp_synt_share * Time_limit
          then
            #tgi_required Data := true
          else
            ();
          !So_far < N andalso check_timer Timer <= Time_limit )
        fun insert E =
          if ( 
              (N_cases=0 andalso 
                if is_q_exp E then min_once_check(Min_once,E) else true)
               orelse 
               min_once_check(Min_once,E) 
              ) andalso 
             (
              not Is_case_exp_pos orelse
              let val app_exp{func,...} = E in
                not( is_constructor func )
              end
              )
          then
            let 
              val Not_activated_syms = exp_flat_map( fn Sub => 
                if is_not_activated_exp Sub then 
                  (case Sub of app_exp{ func, ... } => func::nil) 
                else 
                  nil,
                E)
            in
              if N_cases=0 orelse DUPL orelse 
                 equal_rhs_check( Subst_fun E ) 
              then 
                ( inc N_Buffer; real_inc So_far; Buffer := 
                  (E,Not_activated_syms)::(!Buffer) )
              else
                ()
            end
          else
            ()
        fun flush_buffer() = ( 
          stop_timer Pure_exp_synt_timer;
          stop_timer Exp_synt_timer;
          if N_exps<10.0 then stop_timer Small_exp_synt_timer else ();
          loop(emit,rev(!Buffer)); 
          start_timer Pure_exp_synt_timer;
          start_timer Exp_synt_timer;
          if N_exps<10.0 then start_timer Small_exp_synt_timer else ();
          N_Buffer := 0;  
          Buffer := nil 
          )
        fun emit'(E,_) = (
          (* p"\nemit':  E = "; Print.print_exp' E; nl(); *)
          insert E;
          if !N_Buffer=100 then (
            stop_timer Timer;
            flush_buffer();
            start_timer Timer
            )
          else
            ()
          )
      in   
        case_synt(N_cases,emit',continue);
 (*       output(!std_out, Int.toString(!So_far)^"  "); *)
        flush_buffer();
        delete_timer Timer;
        max2( op<, 0.0, N - !So_far )
      end (* case_synt *)
    val Case_poses = all_poses_filter( fn E =>
      case E of case_exp{...} => not( is_let_val E ) | _ => false,
      #exp Current_prog )
    val No_of_exps_so_far = ref 0
    fun emit'(E,Not_activated_syms) = 
      ( inc No_of_exps_so_far; 
        emit(E,real(!No_of_exps_so_far),Not_activated_syms) )

    fun g( [], _ ) = ()
      | g( (N_cases,Factor) :: Xs, Unused : real ) =
          g( Xs, case_synt( N_cases, emit', Unused + N_exps*Factor ) )
  in
(*
    output( !std_out, "\n\nDesired no of exps = " ^ Real.toString N_exps ^ "   " );
*)
    if DUPL then
      ( case_synt( Max_int, emit', N_exps ); () )
    else if exists( fn Case_pos => is_prefix(snoc(Case_pos,0),Pos), Case_poses )            orelse N_exps<9.0 
    then
      ( case_synt(0,emit',N_exps); () )
    else
      g( No_of_cases_distribution, 0.0 );
    stop_timer Pure_exp_synt_timer;
    stop_timer Exp_synt_timer;
    if N_exps<10.0 then stop_timer Small_exp_synt_timer else ()
(*
    if N_exps > 3.0 andalso !Emitted_count / N_exps < 0.5 (* andalso
       not Is_case_exp_pos *)
    then (
      output( !std_out, "\n\nLow synt_n production:\n\n!Emitted_count =" ^
        Real.toString( !Emitted_count ) ^ "\n" ); 
      print_synt_n_args( Type, Components, Current_prog, Pos, Max_once,
        Min_once, Eq_check, N_exps )
      )
    else
      ()
*)
(*  
  p"\nsynt_n finished";
  flush_out( !std_out )
*)
  end (* synt_n *)
  handle Ex => re_raise(Ex,"Synt_n")

fun cum_pure_exp_synt_time () = check_timer Pure_exp_synt_timer
fun cum_exp_synt_time () = check_timer Exp_synt_timer
fun cum_small_exp_synt_time () = check_timer Small_exp_synt_timer
    
end (* functor Exp_synt_functor *)

