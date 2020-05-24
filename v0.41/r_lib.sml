(* File: r_lib.sml.
   Created 1998-03-25.
   Modified 2000-04-12.
*)

signature R_lib_sig =
sig

val abstract_common_exp : 
  ( 'a, 'b )Ast.e * Ast_lib.pos * ( 'a, 'b )Ast.e -> ( 'a, 'b )Ast.e

val common_scope_check : ( 'a, 'b )Ast.e  * ( 'a, 'b )Ast.e -> bool

val add_not_activated_exps_dec : Ast.dec -> Ast.dec

val replace : real *
    ( int * real )list * bool * Ast.exp list * Ast.exp list * Ast.dec * 
    Ast_lib.pos * Ast_lib.pos list * real * Ast.symbol list list * bool *
    ( Ast.dec * real * Ast.symbol list * 
      { bottom_labels : Ast.exp list, synted_exp : Ast.exp } 
    -> unit ) 
    -> unit
val cum_replace_time : unit -> real

val comps_at_pos : Ast.dec * Ast_lib.pos -> Ast.ty_env

val pat_occ_check : ( 'a, 'b )Ast.e -> bool

val pos_syntactic_complexity 
    : Ast.dec * Ast.exp * 'a list * Ast_lib.pos -> real

val synted_syntactic_complexity :
  Ast.dec * Ast_lib2.R_record -> real

val synted_syntactic_complexity_time : unit -> real

(* val extra_syntactic_complexity : ( 'a, 'b )Ast.e -> real *)

val pos_to_pat_subst : 
  bool * bool * ( 'a, 'b )Ast.d * Ast_lib.pos -> ( 'a, 'b )Ast_lib.exp_subst

(* val nn_post_opt : Ast.dec * real * Ast_lib2.R_record -> Ast.dec option *)

structure Exp_synt : EXP_SYNT
structure So_far : SO_FAR
end


functor R_lib_fn( Exp_synt : EXP_SYNT ) : R_lib_sig =
struct

structure Exp_synt = Exp_synt
structure So_far = So_far_fn( Exp_synt.Synt_lib )

structure Evaluate = Exp_synt.Synt_lib.Evaluate

open Lib List1 Ast Ast_lib Ast_lib2 Print Exp_synt.Synt_lib Evaluate



fun abstract_common_exp( E : ('a,'b)e, Pos : pos, Common : ('a,'b)e )
    : ('a,'b)e =
  let
    val Sub = pos_to_sub( E, Pos )
    val V_exp = gen_var_exp( get_exp_info Common )
    val Sub = apply_exp_subst( Sub, [ ( Common, V_exp ) ] )
  in
    pos_replace( E, Pos, fn _ =>
      case_exp{ exp =  Common, rules = [ mk_new_rule( V_exp, Sub ) ],
        exp_info = get_exp_info Sub } )
  end


fun common_scope_check( Common, let_exp{ dec_list, ... } ) =
      not( exists( fn F => sym_exp_member( F, Common  ), 
                   map( #func, dec_list ) ) )
  | common_scope_check _ = true



fun add_not_activated_exps_dec(D as {func,pat,exp,dec_info}:dec ) 
      : dec =
  let 
    val _ = program_eval_fun D
    val exp = add_not_activated_exps exp
    val exp = 
      if is_not_activated_exp exp then
        gen_dont_know_exp( get_exp_info exp )
      else
        exp
  in
    {func=func,pat=pat,exp=exp,dec_info=dec_info}
  end



exception Comps_at_pos
fun comps_at_pos( D as {func,pat,exp,dec_info=Sch}, Pos : int list )
    : ty_env =
  let fun g _ = nil
    fun f(Comps,E,P::_) =
      case E of
        case_exp{rules,...} =>
          if P = 0 then
            Comps
          else
            comps_in_pat(#pat(nth(rules,P-1))) @ Comps
      | let_exp{dec_list,...} =>
          if P < length dec_list then
            let val {func,pat,exp,dec_info=Sch} = nth(dec_list,P)
            in
              (func,Sch) :: comps_in_pat pat @ Comps
            end
          else
            map( fn{func, dec_info=Sch, ...} => (func,Sch), dec_list ) @
            Comps
      | _ => Comps
  in
    (func,Sch) :: comps_in_pat pat @
    pos_fold(f,g,Pos,exp) @ (!Comps_to_use)
  end
  handle Ex => (
    p"\n\ncomps_at_pos:\n";
    Print.print_dec' D; nl();
    print_pos Pos; nl();
    re_raise(Ex,"Comps_at_pos") )



local


fun exp_eq_violations( E1 : ('a,'b)e,  E2 : ('c,'d)e ) : int =
  case E1 of
    app_exp{func,args,...} => (
      case E2 of app_exp{func=func2,args=args2,...} =>
        if length args <> length args2 then 1 else 
        if func<>func2 then 1 else exp_list_eq_violations (args,args2)
      | _ => 1
      )
  | case_exp{exp,rules,...} => (
      case E2 of case_exp{exp=exp2,rules=rules2,...} =>
        exp_eq_violations(exp,exp2) + (
        if length rules <> length rules2 then 1 else (
          exp_list_eq_violations(map(#exp,rules),map(#exp,rules2)) ) )
      | _ => 1
      )
  | let_exp{dec_list,exp,...} => (
      case E2 of let_exp{dec_list=dec_list2,exp=exp2,...} =>
        exp_eq_violations(exp,exp2) + (
        if length dec_list <> length dec_list2 then 1 else (
        int_sum( map( dec_eq_violations, combine( dec_list, dec_list2 ) )) ) )
      | _ => 1
      )

and dec_eq_violations( {func,pat,exp,...} : ('a,'b)d, 
      {func=func2,pat=pat2,exp=exp2,...} : ('c,'d)d ) : int =
  if func <> func2 
    then 
    1 
  else 
    exp_eq_violations(exp,exp2)

and exp_list_eq_violations([],[]) = 0
  | exp_list_eq_violations(E1::Es1,E2::Es2) = 
      exp_eq_violations(E1,E2) + exp_list_eq_violations(Es1,Es2)


fun top_level_eq( app_exp{ func, ... }, app_exp{ func = func2, ...} ) =
      func = func2
  | top_level_eq( case_exp{ ... }, case_exp{ ... } ) = true
  | top_level_eq( let_exp{ ... }, let_exp{ ... } ) = true
  | top_level_eq( _, _ ) = false

fun matches( E1, E2 ) =
  is_dont_know_exp E1 andalso is_dont_know_exp E2 orelse
  is_not_activated_exp E1 andalso is_not_activated_exp E2 orelse
  top_level_eq( E1, E2 ) andalso exp_eq_violations( E1, E2 ) <= 1




fun build_case( E : exp, V : exp, RHS : exp ) : exp =
(* case E of V => RHS *)
let
in 
  case_exp{ exp = E, rules = [ mk_new_rule( V, RHS ) ],
    exp_info = get_exp_info RHS }
end

fun bottom_subst( E : exp, Labels : exp list ) : exp =
let
  val Counts = map( fn Label => 
    exp_count( fn Sub => exp_eq( Sub, Label ), E ),
    Labels )

  fun g( [], [], E ) = E
    | g( Count :: Counts, Label :: Labels, E ) =
    if Count = 0 orelse Count = 1 then
      g( Counts, Labels, E )
    else
      g( Counts, Labels, 
      let
        val New_label = gen_var_exp( get_exp_info Label )
        val E = apply_exp_subst( E, [ (Label,New_label) ] )
      in
        build_case( Label, New_label, E )
      end )
        
in
  g( Counts, Labels, E )
end



in (* local *)

val replace_timer = mk_timer "replace_timer"
fun cum_replace_time() = check_timer replace_timer

fun replace( Synt_and_eval_time_per_exp : real,
    No_of_cases_distribution : (int * real )list,
    NN_synt : bool,
    Old_Es : exp list, Allowed : exp list, 
    D as {func,pat,exp,dec_info} : Ast.dec,
    Top_pos : Ast_lib.pos, Bottom_poses : Ast_lib.pos list, 
    Cost_limit : real, Min_once : Ast.symbol list list, Eq_check : bool,
    emit : 
      Ast.dec * real * Ast.symbol list * 
      { bottom_labels : Ast.exp list, synted_exp : Ast.exp } 
      -> unit  ) : unit =
let
  val _ = start_timer replace_timer
  val emit = fn X => 
    ( stop_timer replace_timer; emit X; start_timer replace_timer )
in (
  if Cost_limit<3.0 then 
    if NN_synt orelse not(null Bottom_poses) then () else
    let 
      val Type = type_of_exp( pos_to_sub(exp,Top_pos) )
      val Es : exp list = flat_map( fn(F,{schematic_vars,ty_exp}) =>
        if is_fun_type ty_exp then
          nil
        else
        case match(ty_exp,Type) of
          NONE => nil
        | SOME _ => app_exp{ func=F, args=nil, exp_info=Type } :: nil,
        !Comps_to_use )
      val Es = take( floor Cost_limit, Es )
    in
      map( fn( E, N ) => 
          emit( 
            pos_replace_dec( D, Top_pos, fn Sub => E ), 
            real N, 
            nil,
            { bottom_labels = [], synted_exp = E } ),
        combine( Es, fromto(1,length Es) ) );
      ()
    end
  else
    if NN_synt andalso exists( fn Bottom_pos => 
      Rconst.is_rconst_type( type_of_exp( pos_to_sub( exp, Bottom_pos ) ) ),
      Bottom_poses )
    then
      ()
    else
  let 
    val Emitted_count = ref 0
    val Labelled_bottoms =
      map( fn Bottom_pos =>
        ( gen_var_sym(), pos_to_sub(exp,Bottom_pos) ),
        Bottom_poses)

    val Comps_at_pos_in_D = comps_at_pos( D, Top_pos )

    val Comps_at_pos_in_D = if not NN_synt then Comps_at_pos_in_D else
      filter( fn( Sym, _ ) => is_variable Sym orelse
        Sym = PHI orelse Sym = LIN orelse Sym = CONST,
        Comps_at_pos_in_D )

    val Components = 
      map( fn(Sym,Bottom_exp) =>
        (Sym,{schematic_vars=nil,ty_exp=type_of_exp Bottom_exp}),
        Labelled_bottoms
        ) @
      Comps_at_pos_in_D

    val Min_once' = map( fn X => X::nil, map(#1,Labelled_bottoms)) @ Min_once
    val Exp_subst =
          combine(
            map( fn(Sym,Bottom_exp) =>
              app_exp{ func=Sym, args=nil, 
                exp_info=type_of_exp Bottom_exp },
              Labelled_bottoms),
            map(#2,Labelled_bottoms) )
    val Labels = map( #1, Exp_subst )
    fun Subst_fun E = 
      apply_exp_subst( bottom_subst( E, Labels ), Exp_subst )
    fun emit_synted_exp( Raw_E : exp, Cost : real, 
          Not_activated_syms : symbol list ) : unit =
      case Subst_fun Raw_E of E =>
      if exists( fn Old_E => matches( Old_E, E ), Old_Es ) andalso
         not( member'( exp_eq, E, Allowed ) )
         orelse
         is_q_exp E andalso (
             null Top_pos orelse not(is_case_exp(pos_to_sub(exp,lt Top_pos)))
             orelse dh Top_pos = 0 )
      then 
        () 
      else (
        inc Emitted_count;
        emit( { func = func, pat = pat, 
            exp = pos_replace( exp, Top_pos, fn _ => E ),
            dec_info = dec_info},
          real( !Emitted_count ), Not_activated_syms,
          { bottom_labels = map( #1, Exp_subst ), 
            synted_exp = bottom_subst( Raw_E, Labels ) } )
       )
  in
    Exp_synt.synt_n( Synt_and_eval_time_per_exp, No_of_cases_distribution,
      NN_synt,
      NONE, type_of_exp(pos_to_sub(exp,Top_pos)), Components, 
      Subst_fun, D, Top_pos, [], Min_once', 
      Eq_check, emit_synted_exp, Cost_limit )
  end ); (* fun replace *)
  stop_timer replace_timer
end
  handle Ex => (
  p"\n\nreplace:\n";
  p"  D = \n"; Print.print_dec' D; nl();
  p"  Cost_limit = "; p( Real.toString Cost_limit ); nl();
  p"  Min_once = "; print_list( fn Xs => 
    print_list( fn Sym => p( symbol_to_string Sym ), Xs ),
    Min_once ); nl();
  p"  Eq_check = "; p( Bool.toString Eq_check );nl();
  p"  Top_pos = "; print_pos Top_pos; nl();
  p"  Bottom_poses = "; print_pos_list Bottom_poses; nl();
  nl(); 
  re_raise(Ex,"Replace") 
  )


end (* local *)



fun pat_occ_check( case_exp{ rules, ... } ) =
  exists( fn{ pat, exp, ... } =>
    exists( fn V => sym_exp_member( V, exp ), vars_in_pat pat ),
    rules )
  | pat_occ_check _ = true

local

fun bad_count E = exp_count( fn Sub => not( pat_occ_check Sub ), E )

fun closest_dec( D as { exp, ... }, Pos ) =
  let
    fun f( X_opt, Sub, Pos ) =
      case X_opt of
        SOME X => SOME X
      | NONE =>
      case Sub of
        let_exp{ dec_list, ... } =>
          if hd Pos < length dec_list then
            SOME( nth( dec_list, hd Pos ), tl Pos )
          else
            NONE
      | _ => NONE
    
    fun g _ = NONE
  in
    case pos_fold( f, g, Pos, exp ) of
      NONE => ( D, Pos )
    | SOME X => X
  end

fun tgi_count( E : exp, TGI_args : TGI.TGI_args_type ) : int =
let
  fun tcs Es = int_sum( map( fn E => tgi_count( E, TGI_args ), Es ) )
in
  case E of
    app_exp{ func, args, ... } => (
      case assoc_opt( func, TGI_args ) of
        NONE => tcs args
      | SOME Par_subs_list =>
      case map( #2, Par_subs_list ) of Argss =>
      ( if exists( fn( Arg, Args ) => member'( exp_eq, Arg, Args ),
                   combine( args, Argss ) )
        then
          1
        else
          0 ) + tcs args )
  | case_exp{ exp, rules, ... } => tgi_count( exp, TGI_args ) + 
      int_sum( map( fn( { exp, ... }, I ) =>
        tgi_count( exp, TGI.fill_in_tgi_args( E, TGI_args, [I] ) ),
        indexize( rules, 1 ) ) )
end (* fun tgi_count *)

fun is_tgi_arg( D, E, Pos ) : bool =
  if null Pos then false else
  case (lt Pos, dh Pos) of ( Parent_pos, Child_no ) =>
  case pos_to_sub( #exp D, Parent_pos ) of 
    app_exp{ func, args, ... } =>
    let
      val TGI_args = TGI.tgi_args( D, Parent_pos ) 
    in
      case assoc_opt( func, TGI_args ) of
        NONE => false
      | SOME Par_subs_list =>
      case map( #2, Par_subs_list ) of Argss => 
        member'( exp_eq, E, nth( Argss, Child_no ) ) 
    end
  | _ => false
  
in (* local *)
            
exception Pos_syntactic_complexity
fun pos_syntactic_complexity( D, E, Bottom_labels, Pos ) : real =
  let
    val No_globals = #2( Produce_super_combs.make_super_combs [ D ] )
    val Comps = comps_at_pos( D, Pos )
    fun n_leaves( Comps : ty_env ) = length( 
      filter( fn( _, { ty_exp, ... } ) => not( is_fun_type ty_exp ), 
        Comps ) )
    val N_internals = length Comps - n_leaves Comps
    val ( Closest, Closest_pos ) = closest_dec( D, Pos )
    val Closest_comps = comps_at_pos( Closest, Closest_pos )
    val Is_super = 
      case Symbol_HashTable.find No_globals (#func Closest) of
        NONE => false
      | SOME _ => true
    val N_leaves =
      if Is_super then
        n_leaves Closest_comps
      else
        n_leaves Comps
    val N_leaves = N_leaves + length Bottom_labels
    val Normal_lengths = ( ~(ln 0.025), ~(ln 0.15), ~(ln 0.325), ~(ln 0.5) )
    val ( _, _, Internal, _ ) = Normal_lengths
    val Argument_lengths = Normal_lengths
    val Analyzed_lengths = Normal_lengths 
    val TGI_args = TGI.tgi_args( D, Pos ) 
    val TGI_count = tgi_count( E, TGI_args )
    val Syms_and_mults = Ast_lib3.syms_and_mults E
    val Total_TGI_fun_count = int_sum(
      map( fn F => 
        case Symbol_HashTable.find Syms_and_mults F of NONE => 0 | SOME N => N, 
        map( #1, TGI_args ) ) )
    val Non_TGI_count = Total_TGI_fun_count - TGI_count
    val Is_tgi_arg = is_tgi_arg( D, E, Pos )
  in
    sc_of_exp( Normal_lengths, Normal_lengths, N_internals, N_leaves, 
      false, Normal_lengths, E, No_globals ) + 
    real( bad_count E ) * 3.0 * (~(ln 0.15))  -
    real TGI_count * ln( real N_leaves ) * 0.7 +
    real Non_TGI_count * ( Internal + ln( real N_internals ) ) * 0.7 -
    (if Is_tgi_arg then 0.7 * ln( real N_leaves ) else 0.0)
    
  end
  handle Ex => (
  p"\n\npos_syntactic_complexity:\n";
  p"  D = \n"; Print.print_dec' D; nl();
  p"  E = \n"; Print.print_exp' E; nl();
  p"  Pos = "; print_pos Pos; nl();
  nl(); 
  re_raise(Ex,"pos_syntactic_complexity") 
  )


end (* local *)




fun synted_syntactic_complexity( D, 
      { r_top_poses = ( Alt, Stand_in_opt ), synted_exp, 
        bottom_labels, ... } : R_record
      ) : real = 
    if null Alt then (* Sentinel meaning identity R. *)
      0.0
    else
    let
      val E =
        case Stand_in_opt of
          NONE => synted_exp
        | SOME( Stand_in, Pos ) => 
            pos_replace( Stand_in, Pos, fn _ => synted_exp )
      val Pos =
        case Alt of
          [ Top_pos ] => Top_pos
        | _::_::_ => longest_common_prefix Alt 

    in 
      pos_syntactic_complexity( D, E, bottom_labels, Pos )
    end (* fun synted_syntactic_complexity *)

val Synted_syntactic_complexity_timer = mk_timer "synted_syntactic_complexity"

fun synted_syntactic_complexity_time() =
  check_timer Synted_syntactic_complexity_timer

val synted_syntactic_complexity = fn X =>
  let
    val () = start_timer Synted_syntactic_complexity_timer
    val Y = synted_syntactic_complexity X
  in
    stop_timer Synted_syntactic_complexity_timer;
    Y
  end


(* 

Not currently used:

fun extra_syntactic_complexity( E : ( 'a, 'b )e ) : real =
let
  val Sum = ref 0.0
  val Occurring_syms = occurring_syms E
  fun occurs Sym = Symbol_set.member( Sym, Occurring_syms )
  fun add() = Sum := !Sum + 2.0 * (~(ln 0.15))
  fun s( app_exp{ func, args, ... } ) = ( map( s, args ); () )
    | s( case_exp{ exp, rules, ... } ) = ( 
        s exp;
        map( fn { exp, ... } => s exp, rules ); (
        if exists( fn{ pat, ... } => exists( occurs, vars_in_pat pat ),
                   rules )
        then
          ()
        else
          add()
        ) )
    | s( let_exp{ dec_list, exp, ... } ) = (
        s exp;
        map( fn { exp, ... } => s exp, dec_list );
        ()
        )
in
  s E;
  !Sum
end
*)

fun pos_to_pat_subst( Ignore_var_case_rule, Require_var_pat, D, Pos ) = 
  let
    val Subst = Ast_lib2.pos_to_pat_subst'( 
                      Ignore_var_case_rule, Require_var_pat, D, Pos )
  in
    filter( fn( _, To ) =>
      null( Symbol_set.set_to_list( 
        Symbol_set.intersection( 
          !Evaluate.Semi_abstract_constructors,
          occurring_syms To ) ) ),
      Subst )
  end


local

(* Copied from synt_lib.sml: *)


fun contains_case_exp E = exp_count( is_case_exp, E ) > 0


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

structure H = Symbol_HashTable

exception NN_post_opt_exn
fun case_beta_expansion E =
(* Unfolding of constants defined by single rule case-expressions. *)
  let
    val Dangerous_case_beta_expanded = ref false
    val Table : int H.hash_table = H.mkTable( 2, NN_post_opt_exn )

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
    let
      val Be_generous =
        case E of 
          app_exp{ func, ... } => if func = PHI then false else true
        | _ => true
      val Generosity = if Be_generous then 10 + 4 * exp_size E else 0
    in
      if mult V <= 1 orelse ( 
         not( contains_f_or_g E ) andalso
         1 + exp_size E + mult V >= exp_size E * mult V - Generosity )
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
    end
  in (
    exp_map( 
      fn Sub as app_exp{ func, args = nil, ... } => ( insert func; Sub )
       | Sub as case_exp{ exp, 
                  rules = Rules as [ { pat, exp = Rhs, ... } ], ... } => (
           case pat of
             app_exp{ func, args = nil, ... } =>
               if is_variable func then (
                 case length Rules >= 2 of false => ();
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
in

(*
fun nn_post_opt( D : dec, Cost : real, 
      Trf_history : Ast_lib2.R_record ) : dec option =
let
  val ( E, _ ) = 
(*
    if NN_lib.is_nn( #exp D ) then 
      (#exp D,false) 
    else 
*)
      case_beta_expansion( #exp D )
in
  if not( NN_lib.is_nn E ) then (
(*
    p"\n E = \n"; Print.print_exp' E;
    Ast_lib2.print_R_record Trf_history; nl();
*)
    NONE 
    )
  else SOME
let
  val D = set_exp( D, E )
  val New_D = Exp_synt.Synt_lib.NN_opt.opt( D, Cost )
(*
  val New_Ds = map( fn Cost => Exp_synt.Synt_lib.NN_opt.opt( D, Cost ),
    [ 32.0, 64.0, 128.0, 256.0 ] )
*)
in
(*
  nl();
  Ast_lib2.print_R_record Trf_history; nl();
  Evaluate.pre D; nl();
  loop(fn New_D => ( Evaluate.pre New_D; nl() ), New_Ds );
  nl();
 dh New_Ds
  *)
  New_D
end
end
*)

end (* local *)
  


        
end (* functor R_lib_fn *)
