(*
  File: super_combs.sml.
  Created: 1996-06-17.
  Modified: 1999-02-02.
*)

signature PRODUCE_SUPER_COMBS =
sig

val make_super_combs 
    : ('1a,'1b)Ast.d list -> 
      Ast.dec list * unit Ast.Symbol_HashTable.hash_table
(* NOTE: Type information is destroyed. *)

val add_act_indices : ('1a,'1b)Ast.d list * int -> int

end

structure Produce_super_combs : PRODUCE_SUPER_COMBS =
struct
open Lib List1 Ast Ast_lib

structure H = Symbol_HashTable

exception Produce_occurrrence_table_exn
fun produce_occurrence_table( Es : ( 'a, 'b )e list ) : unit H.hash_table =
let
  val T = H.mkTable( 100, Produce_occurrrence_table_exn )
  fun ins Sym =
    if is_variable Sym then
      H.insert T ( Sym, () )
    else
      ()
  fun l( app_exp{ func, args, ... } ) = ( ins func; loop( l, args ) )
    | l( case_exp{ exp, rules, ... } ) = 
        ( l exp; loop( fn{ exp, ... } => l exp, rules ) )
    | l( let_exp{ dec_list, exp, ... } ) = 
        ( l exp; loop( fn{ exp, ... } => l exp, dec_list ) )
in
  loop( l, Es );
  T
end
  
    

fun add_act_indices( Ds : ('1a,'1b)d list, Initial_act_index : int ) 
    : int =
  (* Sets consecutive indices in all case-lhs'es. *)
  let
    val Current = ref Initial_act_index
    fun next() = let val Curr = !Current in inc Current; Curr end
    fun add_e( app_exp{ args, ...} ) = loop( add_e, args )
      | add_e( case_exp{ exp, rules, ... } ) = (
          add_e exp;
          loop( fn { pat, exp, act_index, act_count, activated } => (
              add_e exp;
              act_index := next();
              activated := false),
            rules )
           )
      | add_e( let_exp{ dec_list, exp, ... } ) = (
          loop( add_d, dec_list );
          add_e exp
          )
      | add_e _ = ()
    and add_d { exp, ... } = add_e exp
  in
    loop( add_d, Ds );
    !Current
  end (* fun add_act_indices *)



fun as_elim_pat( Pat : ('1a,'1b)e ) 
    : ('1a,'1b)e * (('1a,'1b)e -> ('1a,'1b)e) =
  case Pat of
    app_exp{ func, args, exp_info } =>
      let
        val ( Ps, Fs ) = split(map( as_elim_pat, args ))
      in
        ( app_exp{ func = func, args = Ps, exp_info = exp_info },
          let
            fun g [] = (fn E => E)
              | g( F::Fs ) = case g Fs of G => (fn E => F(G E))
          in
            g Fs
          end )
      end
  | as_exp{ var, pat, exp_info } =>
      let
        val ( P, F ) = as_elim_pat pat
        val Var_exp = 
          app_exp{ func = var, args = [], exp_info = exp_info }
      in
        ( Var_exp,
          fn E => 
            let
              val Rhs = F E
            in
              case_exp{
                exp = Var_exp,
                rules = [ mk_new_rule( P, Rhs ) ],
                exp_info = get_exp_info Rhs }
            end )
      end


fun as_elim_dec { func, pat, exp, dec_info } =
  let
    val ( P, F ) = as_elim_pat pat
  in
    { func = func, pat = P, exp = F( as_elim_exp exp ),
      dec_info = dec_info }
  end

and as_elim_exp E =
  case E of
    app_exp{ func, args, exp_info } =>
      app_exp{ func = func, args = map( as_elim_exp, args ),
        exp_info = exp_info }
  | case_exp{ exp, rules, exp_info } =>
      case_exp{ exp = as_elim_exp exp,
        rules = map( fn Rule as { pat, exp, ... } =>
          let
            val ( P, F ) = as_elim_pat pat
          in
            mk_rule( Rule, P, F( as_elim_exp exp ) )
          end,
          rules ),
        exp_info = exp_info }
  | let_exp{ dec_list, exp, exp_info } =>
      let_exp{
        dec_list = map( as_elim_dec, dec_list ),
        exp = as_elim_exp exp,
        exp_info = exp_info }





exception Produce_level_table'

exception Variable_names_not_unique_exn
fun produce_level_table( Ds : ('1a,'1b)d list ) : int H.hash_table =
  let
    fun r Sym = (
      p"\nproduce_level_table: "; p( symbol_to_string Sym ); nl();
      raise Variable_names_not_unique_exn
      )
    val Level_table : int H.hash_table =
      H.mkTable( 1000, Produce_level_table' )
    fun traverse_d( 
          { func, pat, exp, ... } : ('1a,'1b)d, 
          Level : int ) : unit = (
      (* Test not to give level 1 to predefined functions. *)
      case H.find Level_table func of
        NONE => H.insert Level_table (func,Level)
      | SOME _ => ();
      loop( fn Par => 
        case H.find Level_table Par of
          NONE => H.insert Level_table (Par,Level)
        | SOME _ => r Par,
           vars_in_pure_tuple_pat pat );
      traverse_e( exp, Level )
      )
    and traverse_e( E : ('1a,'1b)e, Level ) =
      case E of
        app_exp{ func, args, ... } => (
          if is_int func orelse is_real func orelse is_q func then
              case H.find Level_table func of
                NONE => H.insert Level_table (func,0)
              | SOME _ => if is_q func then r func else ()
          else
            ();
          loop(fn E => traverse_e(E,Level), args )
          )
      | case_exp{ exp, rules, ... } => (
          traverse_e( exp, Level );
          loop( fn {pat,exp,...} => (
            loop( fn Var =>
              case H.find Level_table Var of
                NONE => H.insert Level_table (Var,Level)
              | SOME _ => r Var,
                  vars_in_pat pat );
            traverse_e( exp, Level )
            ),
            rules 
            )
          )
      | let_exp{ dec_list, exp, ... } => (
          loop( fn D => traverse_d( D, Level+1 ), dec_list );
          traverse_e( exp, Level )
          )
  in
    loop( fn (Sym,_) => H.insert Level_table (Sym,0),
         Predefined.ty_env() );
    H.insert Level_table ( TUPLE, 0 );
    loop( fn D => traverse_d(D,1), Ds );
    Level_table
  end (* produce_level_table *)
        
 
exception Produce_extra_args_tables
fun produce_extra_args_tables( Ds : ('1a,'1b)d list,
      Level_table : int H.hash_table ) 
    : '1a H.hash_table H.hash_table * 
      unit H.hash_table H.hash_table =
(* Produces Extra_args_tables and Func_dep_table. *)
let
  val Extra_args_tables 
      : '1a H.hash_table H.hash_table =
    H.mkTable( 100, Produce_extra_args_tables )
  val Func_dep_table : unit H.hash_table H.hash_table =
    H.mkTable( 100, Produce_extra_args_tables )
  fun level( S : symbol ) : int = H.lookup Level_table S
  handle Ex => (
    output(!std_out, "level: " ^ symbol_to_string S);
    flush_out( !std_out );
    Print.print_decs' Ds;
    raise Ex
    )
  fun extra_args_dec( { func, exp, ... } : ('1a,'1b)d,
        Level : int ) : unit =
    let
      val Extra_args_table = 
        H.mkTable( 10, Produce_extra_args_tables )
      val Dep_table = 
        H.mkTable( 10, Produce_extra_args_tables )
    in
      H.insert Func_dep_table ( func, Dep_table );
      H.insert Extra_args_tables ( func, Extra_args_table );
      extra_args_exp( exp, func, Dep_table, Extra_args_table, 
        Level )
    end
  and extra_args_exp( E : ('1a,'1b)e, F, Dep_table, Extra_args_table, 
        Level ) : unit =
    let fun extr E = 
      case E of
        app_exp{ func, args, exp_info } => (
          case args of
            nil =>
              let val L = level func in
                if 0 < L andalso L < Level then
                  H.insert Extra_args_table ( func, exp_info )
                else
                  ()
              end
          | _ => ( 
            if level func > 0 then
              H.insert Dep_table (func,())
            else
              ();
            loop( extr, args ) ) )
      | case_exp{ exp, rules, ... } => (
          extr exp;
          map( fn{ pat, exp, ... } => extr exp, rules );
          () )
      | let_exp{ dec_list, exp, ... } => (
          loop( fn D => extra_args_dec( D, Level+1 ), dec_list );
          extr exp )
    in
      extr E
    end
in
  loop( fn D => extra_args_dec( D, 1 ), Ds );
  ( Extra_args_tables, Func_dep_table )
end (* fun produce_extra_args_tables *)

exception Propagate_extra_args_exn
fun propagate_extra_args( 
      Start : symbol,
      So_far : unit H.hash_table H.hash_table,
      level : symbol -> int,
      children : symbol -> symbol list,
      Extra_args_tables : '1a H.hash_table H.hash_table
      ) : unit =
(* Propagates the extra args of the function Start to all its descendants.
   Note that the extra args are filtered for each node visited.
*) 
  let
    fun extras F = H.listItemsi( H.lookup Extra_args_tables F )
    fun g( Current : symbol, Extras : ( symbol * '1a ) list ) : unit =
      let
        val Extras = extras Current @ Extras
        val Extras_so_far_table = H.lookup So_far Current
        val Extras = filter( fn( X, _ ) =>
          case H.find Extras_so_far_table X of
            NONE => true
          | SOME _ => false,
          Extras )
        val L = level Current
        val Extras = filter( fn( Arg, Exp_info ) => level Arg < L,
          Extras )
      in
        case Extras of
          nil => ()
        | _ =>
            let
              val _ = 
                loop( fn( X, _ ) => 
                  H.insert Extras_so_far_table ( X, () ),
                  Extras )
              val Table = H.lookup Extra_args_tables Current
            in
              loop( fn X => H.insert Table X, Extras );
              loop( fn Child => g( Child, Extras ), children Current )
            end
      end
  in
    g( Start, nil )
  end
    
          
exception Update_extra_args_tables_exn
fun update_extra_args_tables (
      Level_table : int H.hash_table,
      Extra_args_tables : '1a H.hash_table H.hash_table,
      Func_dep_table : unit H.hash_table H.hash_table
      ) : unit =
  let
    fun level X = H.lookup Level_table X
    fun children F = map( #1, H.listItemsi( H.lookup Func_dep_table F ) )
    val So_far =
      H.mapi 
        ( fn _ => H.mkTable( 2, Update_extra_args_tables_exn ) 
                  : unit H.hash_table ) 
        Func_dep_table
  in
    H.appi ( fn( F, _ ) => 
      propagate_extra_args( F, So_far, level, children, 
        Extra_args_tables ) )
      Extra_args_tables
  end

exception Reverse_graph_exn
fun reverse_graph( Func_dep_table : unit H.hash_table H.hash_table ) 
    : unit H.hash_table H.hash_table =
  let
    val New_table : unit H.hash_table H.hash_table =
      H.mapi 
        ( fn _ => H.mkTable( 2, Reverse_graph_exn ) : unit H.hash_table ) 
        Func_dep_table
  in
    H.appi ( fn( Parent, Children ) =>
      H.appi ( fn( Child, () ) =>
        if Child = Parent then
          ()
        else
        let
          val Table = H.lookup New_table Child
        in
          H.insert Table ( Parent, () )
        end )
        Children )
      Func_dep_table;
    New_table
  end




exception No_globals_exn
exception Lambda_lift
exception Lambda_lift_exn2
fun lambda_lift( Ds : ('1a,'1b)d list ) 
    : dec list * unit H.hash_table =
let
  val No_globals = H.mkTable( 2, No_globals_exn )
  val Occurrence_table = produce_occurrence_table( map( #exp, Ds ) )
  val Level_table = produce_level_table Ds
  val ( Extra_args_tables, Func_dep_table ) = 
    produce_extra_args_tables ( Ds, Level_table )
  val Func_dep_table = reverse_graph Func_dep_table
  val _ = 
    update_extra_args_tables( Level_table,
      Extra_args_tables, Func_dep_table )
  
  fun lookup Func = H.lookup Extra_args_tables Func
  fun find Func = H.find Extra_args_tables Func
  fun mk_args Xs = map( fn(Sym,Exp_info) =>
    app_exp{ func = Sym, args = [], exp_info = Dummy_ty_exp },
    H.listItemsi Xs )
  fun lambda_lift_d( { func = Func, pat, exp, dec_info } : ('1a,'1b)d )
      : dec list =
    let
      val ( New_exp, Decs ) = lambda_lift_e exp
      val New_pat =
        let
          val Extra_args = mk_args( lookup Func )
          val app_exp{ func, args, exp_info } = pat
        in
        case Extra_args of
          nil => ( H.insert No_globals ( Func, () ); remove_types pat )
        | _ =>
        case args of
          nil => app_exp{
            func = TUPLE,
            args = remove_types pat::Extra_args,
            exp_info = Dummy_ty_exp }
        | _ =>
          if func <> TUPLE then
            raise Lambda_lift
          else
            app_exp{
              func = TUPLE,
              args = map( remove_types, args ) @ Extra_args,
              exp_info = Dummy_ty_exp }
        end
    in
      { func = Func, pat = New_pat, exp = New_exp,
        dec_info = Dummy_ty_schema } ::
      Decs
    end (* fun lambda_lift_d *)

  and lambda_lift_e( E : ('1a,'1b)e ) : exp * dec list =
  case E of
    app_exp{ func, args, exp_info } =>
      let
        val ( New_args, Dss ) = unzip( map( lambda_lift_e, args ) )
        val New_args =
          case find func of
            NONE => New_args
          | SOME Extra_args => New_args @ mk_args Extra_args
      in
        ( app_exp{ func=func, args = New_args, 
            exp_info = Dummy_ty_exp },
          flatten Dss )
      end
  | case_exp{ exp, rules, exp_info } =>
      let
        val ( New_exp, Ds ) = lambda_lift_e exp
        val ( New_rules, Dss ) = 
          unzip( map( fn Rule as { pat, exp, ... } =>
          let 
            val ( New_exp, Ds ) = lambda_lift_e exp
            val app_exp{ func, args, exp_info } = pat
            val pat = app_exp{ func = func, args = 
              map( fn Var as app_exp{ func, args=[], exp_info } =>
                if not( is_variable func ) then
                  raise Lambda_lift_exn2
                else
                case H.find Occurrence_table func of
                  NONE => mk_anon_exp Dummy_ty_exp
                | SOME _ => app_exp{ func = func, args=nil, 
                                     exp_info = Dummy_ty_exp },
                args ),
              exp_info = Dummy_ty_exp }
          in
            ( mk_rule( Rule, remove_types pat,  New_exp ), Ds )
          end,
          rules ) )
      in
        ( case_exp{ exp = New_exp, rules = New_rules, 
            exp_info = Dummy_ty_exp },
          Ds @ flatten Dss )
      end
  | let_exp{ dec_list, exp, exp_info } =>
      let
        val Dss = map( lambda_lift_d, dec_list )
        val ( New_exp, Ds ) = lambda_lift_e exp
      in
        ( New_exp, Ds @ flatten Dss )
      end
in
  ( flat_map( lambda_lift_d, Ds ), No_globals )
end (* fun lambda_lift *)

              
       

fun make_super_combs( Ds : ('1a,'1b)d list ) 
    : dec list * unit H.hash_table =
  lambda_lift( map( as_elim_dec, Ds ) )



end (* structure Produce_super_combs *)



