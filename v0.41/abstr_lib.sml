(* File: abstr_lib.sml
   Created 1998-02-12.
   Modified 1999-08-15.
*)

structure Abstr_lib_alt :
  sig
    type alt = Ast_lib.pos list
    val print_alt : alt -> unit
    val print_alt_list : alt list -> unit
    type alt_id = int
    structure Root : HASH_SET
    type alt_data = {
      symbol_table : alt Vector.vector,
      anc_desc_table : alt_id list Vector.vector,
      roots : Root.set,
      roots_covered : Root.set Vector.vector
      }
    val init : Ast.exp * Ast.symbol list * ( Ast.exp -> bool ) * real * real ->
               alt_data
    val list_alt_ids : alt_data -> alt_id list
    val alt_id_to_alt : alt_data * alt_id -> alt
    val no_of_alts : alt_data -> int
    val anc_desc : alt_data * alt_id * alt_id -> bool
    val roots : alt_data -> Root.set
    val roots_covered : alt_data * alt_id -> Root.set
  end =
struct

open Lib List1 Ast Ast_lib Ast_lib6

type alt = pos list
type alt_id = int

val print_alt = print_pos_list
fun print_alt_list Xs =
  print_list( fn X => (nl(); print_alt X), Xs )

structure Root = Int_set

type alt_data = {
  symbol_table : alt Vector.vector,
  anc_desc_table : alt_id list Vector.vector,
  roots : Root.set,
  roots_covered : Root.set Vector.vector
  }

fun list_alt_ids( { symbol_table, ... } : alt_data ) =
  fromto( 0, Vector.length symbol_table - 1 )

fun no_of_alts( { symbol_table, ... } : alt_data ) : int =
  Vector.length symbol_table

fun alt_id_to_alt( { symbol_table, ... } : alt_data, I : alt_id ) : alt = 
  Vector.sub( symbol_table, I )


fun slow_anc_desc( A1 : alt, A2 : alt ) =
  exists( fn P1 =>
    exists( fn P2 => is_prefix( P1, P2 ) orelse is_prefix( P2, P1 ), A2 ),
    A1 )


fun anc_desc( { anc_desc_table, ... } : alt_data, I : alt_id, J : alt_id ) 
    : bool =
  member( J, Vector.sub( anc_desc_table, I ) )



structure S = Symbol_set

fun root_poses( E : exp, Fun_pat_vars : symbol list ) : pos list =
(* Fun_pat_vars are the old parameters of a function to be embedded. Is nil
   if no embedding is to be performed.
*)
  let
    val Dummy_pos : pos = []
    val Result : pos list ref = ref []
    fun ins P = Result := (rev P) :: (!Result)

    fun g( E : exp, P : pos, Vars : symbol list, Active : bool ) : S.set =
      case E of
        app_exp{ func, args, ... } => (
          case args of
            [] => if is_variable func then S.singleton func else S.empty()
          | _::_ =>
              S.union_map( fn( I, Arg ) => g( Arg, I::P, Vars, Active ),
                combine( fromto( 0, length args - 1 ), args ) )
          )
      | case_exp{ exp, rules, ... } => 
      let
        val Syms = g( exp, 0::P, Vars, Active )
      in
        if Active andalso 
           length rules >= 2 andalso
           not( exists( fn V => S.member( V, Syms ), Vars ) )
        then
          ins( 0::P )
        else
          ();
        S.union( Syms,
          S.union_map( fn( I, { pat, exp, ... } ) =>
            g( exp, I::P, vars_in_pat pat @ Vars, Active ),
            combine( fromto( 1,length rules ), rules ) ) )
      end
      | let_exp{ dec_list, exp, ... } =>
          S.union( 
            S.union_map( fn{ exp, ... } => g( exp, Dummy_pos, [], false ), 
              dec_list ),
            g( exp, length dec_list :: P, Vars, Active ) )
            
  in
    g( E, [], Fun_pat_vars, true );
    !Result
  end
          

        
fun init( Pre_body : exp, Fun_pat_vars : symbol list, 
      scope_check : exp -> bool, Time_limit, Astpe ) : alt_data =
  let
    val Alts : alt list = map( fn [Alt] => Alt,
      produce_bottom_posess_list( Pre_body, [], 1, Time_limit, Astpe ) )
 
    fun alt_ok( Ps : pos list ) : bool =
      scope_check( app_exp{ func = SEMICOLON,
        args = snoc( map( fn P => pos_to_sub( Pre_body, P ), Ps ), Pre_body ),
        exp_info = get_exp_info Pre_body } )
    val Alts = filter( alt_ok, Alts )
    val Symbol_table = Vector.fromList Alts
    fun get I = Vector.sub( Symbol_table, I )
    val N = Vector.length Symbol_table
    val Alt_ids = fromto( 0, N - 1 )
    val Root_poses = root_poses( Pre_body, Fun_pat_vars )
    val Root_poses = combine( fromto( 0, length Root_poses - 1 ), Root_poses )
    val Roots_covered = map( fn I : alt_id =>
      map( #1,
        filter( fn( Id, Root_pos) => slow_anc_desc( [Root_pos], get I ),
          Root_poses ) ),
      Alt_ids )
  in { 
    symbol_table = Symbol_table,
    anc_desc_table = Vector.tabulate( N, fn I => 
      filter( fn J => slow_anc_desc( get I, get J ), 
      Alt_ids ) ),
    roots = Root.list_to_set( map( #1, Root_poses ) ),
    roots_covered = Vector.fromList(
      map( Root.list_to_set, Roots_covered ) )
    }
  end

fun roots( { roots, ... } : alt_data ) = roots
    
val roots_covered = fn( { roots_covered, ... } : alt_data, I : alt_id ) =>
  Vector.sub( roots_covered, I )
      
end (* structure Abstr_lib_alt *)
  

functor Choose_arguments( Synt_lib : SYNT_LIB ) :
  sig

  val abstr_kind_weight : Ast_lib2.abstr_kind -> int

  type data = { 
    program : Ast.dec,
    bottom_poses_ok : Ast_lib.pos list -> bool,
    arity : int,
    memo_tables : ( (bool*bool) * int Ast_lib.Pos_hash.hash_table ) list }

    val init : Ast.dec * (Ast_lib.pos list -> bool) * int -> data
    val no_of_choices : bool * bool * data * Ast_lib.pos * real * real -> int
    val choices : bool * bool * data *  Ast_lib.pos * 
      (Ast.dec * Abstr_lib_alt.alt list * Ast_lib2.abstr_kind -> unit) *
      real * real -> unit

  end =
struct


open Lib List1 Ast Ast_lib Ast_lib2 Print Abstr_lib_alt


fun abstr_kind_weight abstre = 1
  | abstr_kind_weight rec_arg_type_exists = 4
  | abstr_kind_weight other_abstr = 1



local

fun card( _ : alt_id, Rs : Root.set ) : int = Root.H.numItems Rs
fun less( X, Y ) = card X < card Y

structure H = Heap_functor(
  struct
    type elem = alt_id * Root.set
    val op< = less
  end
  )

exception Root_choices_exn
fun root_choices(
      Alt_data : alt_data,
      As : ( alt_id * Root.set ) list, 
      N_roots_left : int,
      Arity_left : int,
      So_far : alt_id list,
      emit : alt_id list -> unit
      ) : unit = (
  if N_roots_left < 0 then raise Root_choices_exn else ();
  if Arity_left = 0 orelse null As then
    ()
  else
  let
    val Bs = H.n_max( Arity_left, As )
  in
  if int_sum( map( card, Bs ) ) < N_roots_left then
    ()
  else
  let
    val ( Alt, Roots ) = max( less, Bs )
    val As = filter( fn( A, _ ) => A <> Alt, As )
    val New_As = 
      filter( fn( A, _ ) => not( anc_desc( Alt_data, Alt, A ) ), As )
    val New_As = 
      map( fn( A, Rs ) => ( A, Root.difference( Rs, Roots ) ), 
        New_As )
  in
    case N_roots_left - Root.H.numItems Roots of N => (
      if N = 0 then emit( Alt :: So_far ) else ();
      root_choices( Alt_data, New_As, N, Arity_left - 1, Alt :: So_far, emit )
      );
    root_choices( Alt_data, As, N_roots_left, Arity_left, So_far, emit )
  end
  end
  )


fun unconstrained_choices(
      Alt_data : alt_data,
      Alts : alt_id list,
      Arity_left : int,
      So_far : alt_id list,
      emit : alt_id list -> unit
      ) : unit =
  if Arity_left = 0 then
    emit So_far
  else if length Alts < Arity_left then
    ()
  else
  let
    val Alt :: Alts = Alts
    val New_Alts =
      filter( fn A => not( anc_desc( Alt_data, Alt, A ) ), Alts )
  in
    unconstrained_choices( Alt_data, New_Alts, Arity_left - 1, 
      Alt :: So_far, emit );
    unconstrained_choices( Alt_data, Alts, Arity_left, So_far, emit )
  end

in (* local *)


fun preliminary_dynamic_choices(
      Old_roots_exist : bool, (* True only if embedding is being done and
       there are roots in the fundef to be embedded. *)
      Alt_data : alt_data,
      Root_alts : ( alt_id * Root.set ) list,
      Other_alts : alt_id list,
      N_roots : int,
      Arity: int,
      emit : alt_id list -> unit
      ) : unit =
  if N_roots = 0 andalso not Old_roots_exist then () else
  if N_roots = 0 then
    unconstrained_choices( Alt_data, Other_alts, Arity, [], emit )
  else
  let
    fun emit_root_choices So_far =
      let
        val Other_alts =
          filter( fn A1 => 
            not( exists( fn A2 => anc_desc( Alt_data, A1, A2 ), So_far ) ),
            Other_alts )

(*
       fun p S = output( !std_out, S )
       fun pa( Xs : alt_id list ) = print_alt_list( 
         map( fn X => alt_id_to_alt( Alt_data, X ), Xs ) )
        val _ = (
          p"\nSo_far = "; pa So_far;
          p"\nOther_alts = "; pa Other_alts;
          p"\n\n\n"
          )
*)

       in
         unconstrained_choices( Alt_data, Other_alts, Arity - length So_far,
           So_far, emit )
       end
  in
    root_choices( Alt_data, Root_alts, N_roots, Arity, [],
      emit_root_choices )
  end


fun preliminary_static_choices(
      Old_roots_exist : bool,
      N_roots : int,
      Alt_data : alt_data,
      Alts : alt_id list,
      Arity : int,
      emit : alt_id list -> unit,
      Roots : Root.set
      ) : unit =
  if N_roots = 0 andalso Old_roots_exist then () else
  let
    fun g( [], Roots ) = Roots
      | g( C::Cs, Roots ) = 
          g( Cs, Root.difference( Roots, roots_covered( Alt_data, C ) ) )

    fun emit' Choices =
      if Root.H.numItems Roots > 0 andalso
         Root.H.numItems( g( Choices, Roots ) ) = 0 then
        ()
      else
        emit Choices
  in
    unconstrained_choices( Alt_data, Alts, Arity, [], emit' )
  end

end (* local *)











(* Assume that 
   H(E1,..,En) -> let fun g(V1,...,Vn) = H(V1,...,Vn) in g(E1,...,En) end is
   an abstraction and that Ei is case-analyzed "above" H(E1,...,En).
   Parts of Ei may then occur in H. A case-exp is in this
   case inserted just above H to relate the parts to Vi.
   Example. Assume that the current program is
   fun f(Xs) =
     case Xs of nil => nil
     | X1::Xs1 => 
     case Xs1 of nil => Xs
     | X2::Xs2 => X1::X2::Xs @ X2::nil
   and that H(E1) = X1::X2::Xs @ X2::nil with E1 = Xs.
   The following case-exp is inserted just above H.
   case V1 of nil => ?(V10)
   | V11::V12 =>
   case V12 of nil => ?(V13)
   | V14::V15 => ?(V16)
 
   After the abstraction the program becomes
   fun f(Xs) =
     case Xs of nil => nil
     | X1::Xs1 => 
     case Xs1 of nil => Xs
     | X2::Xs2 =>
     let fun g(V1) =
       case V1 of nil => ?(V10)
       | V11::V12 =>
       case V12 of nil => ?(V13)
       | V14::V15 => V11::V14::V1 @ V14::nil
     in
       g1(Xs)
     end
*)

local
(* The decs below are used to construct Case_exp_parts which for the example
   above would be
   [ 
   ( Xs, 
    ( [2,2],
      case Xs of nil => ?(V10)
      | V11::V12 =>
      case V12 of nil => ?(V13)
      | V14::V15 => ?(V16),
      [ (X1,V11),(Xs1,V12),(X2,V14),(Xs2,V15)]
      ) ),
    ...
    ].
    The type of Case_exp_parts is ( exp * (pos*exp*(exp_info_type,dec_info_type)exp_subst) ) list.
*)

fun case_exp_to_part( Rhs_type, case_exp{exp,rules,...}, Rule_no ) 
    : pos*exp*(exp_info_type,dec_info_type)exp_subst =
(* Example. case_exp_to_part( `case Xs1 of nil =>... | X2::Xs2=>..., 2 ) =
   ( [2], `case Xs1 of nil => ?(V20) | V21::V22 => ?(V21), 
     [(X2,V21), (Xs2,V22)] ).
*)
  let 
    val Var_exps = flat_map( fn{pat,...} => var_exps_in_pat pat, rules )
    val Renaming = 
      map( fn Var_exp => (Var_exp,gen_var_exp(type_of_exp Var_exp)),
           Var_exps )
    val Rules = 
      map( fn Rule as {pat,exp,...} => 
        mk_rule( Rule,
          apply_exp_subst(pat,Renaming), 
          gen_not_activated_exp Rhs_type),
      rules )
  in
    ( Rule_no::nil, case_exp{exp=exp,rules=Rules,exp_info=Rhs_type},
      Renaming )
  end
    
fun update_case_exp_parts(Rhs_type, CE as case_exp{exp,rules,...}, 
    Rule_no, Cum_case_subs, Case_exp_parts ) =
(* Is called for each case-exp on the path given by Top_pos. Cum_case_subs
   would for the example above be [ (Xs,[X1,Xs1,X2,Xs2]), (Xs1,[X2,Xs2]) ].
*)
  let
    exception Update_case_exp_parts
    val New_part = ( exp, case_exp_to_part(Rhs_type,CE,Rule_no) )
    val Case_exp_parts' = map( fn X as ( E, (Pos,So_far,Subst) ) =>
      if member(exp,assoc(E,Cum_case_subs)) then
        let 
          val 
      (Part_pos, Part_case as case_exp{exp,rules,exp_info}, Part_subst ) =
            case_exp_to_part(Rhs_type,CE,Rule_no)
          val Part_case' = 
            case_exp{ exp=assoc(exp,Subst), rules=rules, 
              exp_info=exp_info }
        in
          ( E, ( Pos@Part_pos, pos_replace(So_far,Pos,fn _ => Part_case'),
                 Part_subst@Subst ) )
        end
      else
        X,
      Case_exp_parts )
  in
    New_part::Case_exp_parts'
  end

in (* local *)

fun construct_case_exp_parts(Top_pos,E) =
let 
val Rhs_type = type_of_exp(pos_to_sub(E,Top_pos))
val Cum_case_subs = cum_case_subs_at_pos(E,Top_pos)
fun construct_case_exp_parts'(Pos,E,Case_exp_parts) =
  case Pos of
    nil => Case_exp_parts
  | P::Ps =>
  let fun constr Sub = construct_case_exp_parts'(Ps,Sub,Case_exp_parts)
  in
    case E of
      app_exp{args,...} => constr(nth(args,P))
    | case_exp{exp,rules,...} =>
        if P=0 then
          constr exp
        else
          construct_case_exp_parts'( Ps, #exp(nth(rules,P-1)),
            update_case_exp_parts(Rhs_type,E,P,Cum_case_subs,Case_exp_parts) )
    | let_exp{dec_list,exp,...} => 
        if P<length dec_list then
          constr(#exp(nth(dec_list,P)))
        else
          constr exp
  end
in
  if is_set(map(#1,Cum_case_subs)) then
    SOME(construct_case_exp_parts'(Top_pos,E,nil))
  else
    NONE
end
handle Ex => (
  output(!std_out,"Top_pos = "); print_int_list Top_pos;
  output(!std_out,"\nE = \n"); print_exp' E;
  re_raise(Ex,"Construct_case_exp_parts")
  )
       
end (* local *)        

local
 
exception Apply_abstre_exn

fun apply_abstre( E : exp, emit : exp * abstr_kind -> unit, Top_pos : pos,
      V_exps : exp list, Es : exp list, Rhs : exp ) : unit =
(* Abstraction based embedding. *)
  if null Top_pos orelse null V_exps then () else
  let
    val Parent = pos_to_sub( E, lt Top_pos )
  in
    if not( is_let_exp Parent ) then raise Apply_abstre_exn else
  let
    val let_exp{ dec_list, exp = In_exp, exp_info } = Parent
  in
    if length dec_list = dh Top_pos then raise Apply_abstre_exn else
  let
    val D as { func, pat, dec_info = { schematic_vars = [], ty_exp }, ... } = 
      nth( dec_list, dh Top_pos )
    val New_domain_type =
      ty_con_exp( TUPLE_TY_CON, 
        map( type_of_exp, V_exps ) @ domain_type ty_exp )
    val Old_V_exps =
      case pat of
        VE as app_exp{ func, args, ... } =>
          if func = TUPLE then args else [ VE ]
      | VE => [ VE ]
    val New_pat =
      app_exp{ func = TUPLE, args = V_exps @ Old_V_exps,
        exp_info = New_domain_type }
    val New_Rhs = exp_map(
      fn Sub as app_exp{ func = F, args, exp_info } =>
        if F = func then
          app_exp{ func = F, args = map( remove_as, V_exps ) @ args, 
                   exp_info = exp_info }
        else
          Sub
      | Sub => Sub,
      Rhs )

    val Total_extra_size = ref 0
    val Max_extra_size = case exp_size E of S => S + S div 2 + 1000
    fun too_big() = !Total_extra_size > Max_extra_size

    val New_In_exp = exp_map(
      fn Sub as app_exp{ func = F, args, exp_info } =>
        if F = func andalso not( too_big() ) then
          case combine( map( remove_as, Old_V_exps ), 
                        map( fn Arg => rename( Arg, false ), args ) )
          of 
          Subst => 
          case map( fn E => apply_exp_subst( E, Subst ), Es ) of Es => (
          Total_extra_size := ( !Total_extra_size + 
            int_sum( map( exp_size, Es ) ) +
            int_sum( map( fn( From, To ) => exp_size From + exp_size To, 
                          Subst ) ) );
          case map( fn E => rename( E, false ), Es ) of Es =>
          app_exp{ func = F, args = Es @ args, exp_info = exp_info } )
        else
          Sub
      | Sub => Sub,
      In_exp )
  in
    if too_big() then () else
  let
    val New_D = { func = func, pat = New_pat, exp = New_Rhs,
      dec_info = { schematic_vars = [], ty_exp =
        ty_con_exp( THIN_ARROW, [ New_domain_type, range_type ty_exp ] ) } }
    val New_let_exp =
      let_exp{ dec_list = list_replace( dec_list, dh Top_pos, New_D ),
        exp = New_In_exp, exp_info = exp_info }
    val As_pat_ids = flat_map( 
      fn as_exp{ pat, ... } => vars_in_pat pat | _ => [],
      Old_V_exps )
  in
    if not( null( symbol_intersection( func :: As_pat_ids, 
                    flat_map( zero_arity_apps, Es ) ) ) )
    then
      ()
    else if exists( fn E => sym_exp_member( func, E ), Es ) then () else
      emit( 
        pos_replace( E, lt Top_pos, fn _ => New_let_exp ),
        abstre )
  end
  end
  end
  end (* apply_abstre *)

structure Abstr_lib2 = Abstr_lib2_fn( Synt_lib )

in (* local *)

fun apply_abstr( Emb_chosen : bool, E : exp, Case_exp_parts, 
      emit : exp * abstr_kind -> unit, Top_pos : pos, Alts : alt list ) : unit =
(* H(E1,..,En) -> let fun g(V1,...,Vn) = H(V1,...,Vn) in g(E1,...,En) end,
   where the exps given by Alts are [E1,...,En]. 
   Calls emit( New_E, true ) when New_E resulted from an ABSTRE instead 
   of an ABSTR.
*)
  let 
    val G = gen_func_sym()
    val Arity = length Alts
    val H_Es = pos_to_sub(E,Top_pos) (* The pre-body. *)
    val Es = map( fn Pos => pos_to_sub(H_Es,Pos), map( hd, Alts ) )
    val Ts = map(type_of_exp,Es)
    val V_exps = map(Predefined.mk_pattern,Ts)
    val Vs = map( fn as_exp{var,...} => var | app_exp{func,...} => func, 
                  V_exps )
    val Range_type = type_of_exp H_Es
    val Domain_type = if Arity=1 then hd Ts else ty_con_exp(TUPLE_TY_CON,Ts)

    fun mk_rhs( H_Es, [], [], [] ) = H_Es
        | mk_rhs( H_Es, E_poses :: Alts, T :: Ts, V :: Vs ) =
      poses_replace( mk_rhs( H_Es, Alts, Ts, Vs ), E_poses,
          fn _ => app_exp{func=V, args=nil, exp_info=T} )

    val V_Es_set = 
      make_set'( fn((V1,E1),(V2,E2)) => exp_eq( E1, E2 ), combine(Vs,Es) )
    fun add_cases(Rhs,V_Es_set) =
      case V_Es_set of
        nil => Rhs
      | (V,E)::V_Es_set =>
      let 
        val Rhs = add_cases(Rhs,V_Es_set)
        val ( t, Subst ) = 
          Abstr_lib2.mk_case_exps_and_subst( E,
            app_exp{ func=V,args=nil, exp_info=type_of_exp E },
            type_of_exp Rhs )

        val Rhs = t( apply_exp_subst( Rhs, Subst ) )
      in
      case assoc_opt(E,Case_exp_parts) of
        NONE => Rhs
      | SOME(Pos,Case as case_exp{exp,rules,exp_info},Subst) => 
          let val Case' = 
            case_exp{exp=app_exp{ func=V,args=nil,
                           exp_info=type_of_exp E },
              rules=rules, exp_info=exp_info }
          in
            pos_replace(Case',Pos, fn _ => apply_exp_subst(Rhs,Subst))
          end
      end
    val Rhs = add_cases(mk_rhs(H_Es,Alts,Ts,Vs),V_Es_set)
    val D = { func=G, pat=
      if Arity=1 then
        hd V_exps
      else
        app_exp{func=TUPLE, args=V_exps, exp_info=Domain_type},
      exp=Rhs,
      dec_info={schematic_vars=nil, ty_exp=
        ty_con_exp(THIN_ARROW,Domain_type::Range_type::nil) }
      }
    val In_exp = app_exp{func=G,args=Es,exp_info=Range_type}
    val Let_exp = let_exp{dec_list=D::nil, exp=In_exp, 
      exp_info=Range_type}
  in
    if Emb_chosen then
      apply_abstre( E, emit, Top_pos, V_exps, Es, Rhs )
    else
      emit( 
        pos_replace( E, Top_pos, fn _ => Let_exp ),
        if exists( fn TE => member( TE, Predefined.rec_types() ), Ts ) then
          rec_arg_type_exists
        else
          other_abstr )
  end (* apply_abstr *)

end (* local *)

fun test_apply_abstr(Emb_chosen,E,Top_pos,Alts) =
  let val Res = ref( [] : ( exp * abstr_kind ) list )
      fun  emit X = Res := ( X :: (!Res) )
    val SOME Case_exp_parts = construct_case_exp_parts(Top_pos,E)
  in
    apply_abstr(Emb_chosen,E,Case_exp_parts,emit,Top_pos,Alts);
    !Res
  end


exception Choose_arguments_exn

type data = { 
  program : Ast.dec,
  bottom_poses_ok : Ast_lib.pos list -> bool,
  arity : int,
  memo_tables : ( (bool*bool) * int Ast_lib.Pos_hash.hash_table ) list }

fun init( Program : dec, bottom_poses_ok : pos list -> bool, Arity : int ) 
    : data = {
  program = Program,
  bottom_poses_ok = bottom_poses_ok,
  arity = Arity,
  memo_tables = 
    map( fn X => ( X, Pos_hash.mkTable( 10, Choose_arguments_exn ) ),
      [ (false,false), (false,true), (true,false), (true,true) ] )
  }


fun choices( Dynamic : bool, Embedding : bool,
      { program, bottom_poses_ok, arity, ... } : data, 
      Top_pos : pos, emit : dec * alt list * abstr_kind -> unit,
      Time_limit : real, Astpe : real ) : unit =
let
  val bottom_poses_ok = fn Poses =>
    bottom_poses_ok( map( fn Pos => Top_pos@Pos, Poses ) )
  val { func, pat, exp, dec_info } = program
  val scope_check = fn E => 
    Synt_lib.scope_check( E, func::nil, vars_in_pat pat) 
  val H_Es = pos_to_sub( exp, Top_pos )
  val Old_roots_exist = not( null( exp_filter(
    fn case_exp{ rules, ... } => length rules >= 2 | _ => false,
    H_Es ) ) )
  val Max_Es_size = exp_size H_Es - 2

  fun g Emb_info =
let
  val Alt_data = Abstr_lib_alt.init( H_Es, Emb_info,
    fn Sub => scope_check( pos_replace( exp, Top_pos, fn _ => Sub ) ),
    Time_limit, Astpe )
    
  val Root_alts = 
    filter( fn( Id, Xs ) => Root.H.numItems Xs > 0,
      map( fn Id => ( Id, roots_covered( Alt_data, Id ) ),  
        list_alt_ids Alt_data ) )
  val Other_alts =
    filter( fn Id => Root.H.numItems( roots_covered( Alt_data, Id ) ) = 0,
      list_alt_ids Alt_data )
  val N_roots = Root.H.numItems( roots Alt_data )
  val Case_exp_parts_opt = construct_case_exp_parts( Top_pos, exp )
in
  case Case_exp_parts_opt of NONE => () | SOME Case_exp_parts =>
let
  fun preliminary_emit( Alt_ids : alt_id list ) : unit =
    let
      val Alts = map( fn X => alt_id_to_alt( Alt_data, X ), Alt_ids )
      val Es_size = int_sum( map( fn Bottom_pos =>
        exp_size( pos_to_sub( H_Es, Bottom_pos ) ),
        flatten Alts ) )
      fun emit'( E, Abstr_kind ) =
        emit(
          { func = func, pat = pat, exp = E, dec_info = dec_info },
          map( fn Alt => map( fn Bottom_pos => Top_pos @ Bottom_pos, Alt ),
            Alts ),
          Abstr_kind ) 
    in
      if Es_size > Max_Es_size orelse
         not( bottom_poses_ok( flatten Alts ) ) orelse
         exists( is_q_exp, map( fn P => pos_to_sub( H_Es, P ), flatten Alts ) )
      then
        ()
      else
        apply_abstr( not( null Emb_info ), exp, Case_exp_parts, emit', 
          Top_pos, Alts )
    end
in
(*
  p"\ng: Emb_info = "; print_syms Emb_info; nl();
  p"  Old_roots_exist = "; print_bool Old_roots_exist; nl();
  p"  N_roots = "; print_int N_roots;
*)
  if Dynamic then
    preliminary_dynamic_choices( Old_roots_exist, Alt_data, Root_alts, 
      Other_alts, N_roots, arity, preliminary_emit )
  else
    preliminary_static_choices( Old_roots_exist, N_roots, Alt_data, 
      map( #1, Root_alts ) @ Other_alts, 
      arity, preliminary_emit, roots Alt_data )
end
end (* fun g *)

  val Emb_info = if null Top_pos then [] else
    let
      val ( Prefix, Last ) = ( lt Top_pos, dh Top_pos )
    in
      case pos_to_sub( exp, Prefix ) of
        let_exp{ dec_list, ... } => 
          if Last < length dec_list then
            vars_in_pat( #pat( nth( dec_list, Last ) ) )
          else
            []
      | _ => []
    end
in
  if not Embedding  then
    g []
  else if null Emb_info then () else g Emb_info
end (* fun choices *)

  


fun no_of_choices'( Dynamic : bool, Embedding : bool,
      Data : data, Top_pos : pos, Time_limit, Astpe ) : int =
  let
    val N = ref 0
    fun emit( _, _, Abstr_kind ) =
      N := !N + abstr_kind_weight Abstr_kind
  in
    choices( Dynamic, Embedding, Data, Top_pos, emit, Time_limit, Astpe );
    !N
  end



fun no_of_choices( 
     Dynamic : bool, Embedding : bool,
     Data as { memo_tables, ... } : data, 
     Top_pos : pos, Time_limit, Astpe ) : int =
  let
    val T = assoc( (Dynamic,Embedding), memo_tables )
  in
    case Pos_hash.find T Top_pos of
      NONE => (
        case no_of_choices'( Dynamic, Embedding, Data, Top_pos, Time_limit, Astpe ) of N => (
          Pos_hash.insert T ( Top_pos, N );
          N
          )
       )
    | SOME N => N
  end


end (* functor Choose_arguments *)
