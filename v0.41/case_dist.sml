(* File: case_dist.sml.
   Created: 1993-08-19.
   Modified: 1999-02-17.
*)
signature CASE_DIST_SIG =
sig

val CASE_DIST_trfs : 
  ( '1a -> Ast.exp_info_type ) * ( '1b -> Ast.dec_info_type ) *
  ('1a,'1b)Ast.d * real list * real * (Ast_lib.pos -> bool) *
  (('1a,'1b)Ast.d * Ast_lib2.atomic_trf_record list * real option list -> unit )
   -> unit

end



functor Case_dist_functor( Exp_synt : EXP_SYNT) : CASE_DIST_SIG =
struct
open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib6 Print Parse 
  Exp_synt Exp_synt.Synt_lib Case_dist_lib

structure H = Lib.Real_HashTable

(* Type of data used to make the code reentrant: *)

type ( 'a, 'b )data = {
  time_out : unit -> bool,
  table : ( int * bool ref ) H.hash_table,
  size_check : ( 'a, 'b )e -> bool
  }

fun print_hash_table( { table, ... } : ( 'a, 'b )data ) : unit =
  loop( fn( Fingerprint : real, ( No_of_moves : int, Found : bool ref ) ) =>
    p( "\n" ^ Real.toString Fingerprint ^ " : " ^
       Int.toString No_of_moves ^ " " ^ Bool.toString( !Found ) ),
    H.listItemsi table )
  

(*
fun set_table( { time_out, table, size_check } : ( 'a, 'b )data, Table ) =
  { time_out = time_out, table = Table, size_check = size_check 
    } : ( 'a, 'b )data
*)

fun to_marked E = info_map(fn Exp_info => (false,Exp_info), 
  fn Dec_info => Dec_info, E )

fun from_marked E = info_map(fn(_,Exp_info) => Exp_info,
  fn Dec_info => Dec_info, E )

fun mark_exp E = 
  if is_abstract_con_exp E then
    E
  else 
    exp_info_replace(E,fn(Marked,Info) => (true,Info))

fun mark_exp_at_pos(E,Pos) = 
  pos_replace(E,Pos,fn Sub => 
    if is_abstract_con_exp Sub then Sub else mark_exp Sub)

fun marked_poses(E : (bool*'1a,'1b)e) = 
  all_poses_filter(fn Sub => #1(get_exp_info Sub), E)

fun is_marked( Marked : bool, _ ) = Marked

exception Set_q_exp_type
fun set_q_exp_type(app_exp{func, args=nil, exp_info=(Marked,_)},Type) = 
  if not( is_q func ) then
    raise Set_q_exp_type
  else
    app_exp{func=func, args=nil, exp_info=(Marked,Type)}




(* Example.
  f(case A of Pat1 => Rhs1 | Pat2 => Rhs2,B) ->
  case A of Pat1 => f(Rhs1,B) | Pat2 => f(Rhs2,B)
*)
fun move_case_outwards'( Data : ( 'k, 'l )data,
      E : (bool*'1a,'1b)e, Arg_no : int, Mark_enable :  bool,
      emit : bool * (bool*'1a,'1b)e -> unit ) : unit =
  if (#time_out Data)() then () else
  let
    val Child = pos_to_sub(E,Arg_no::nil)
    fun mark(Marked,Info) = if Mark_enable then (true,Info) else (Marked,Info)
    fun mark'((Marked,_),(_,Info)) = mark(Marked,Info)
  in
    if is_abstract_con_exp Child then () else
    if is_let_exp E andalso is_app_exp Child then
      schema5a( E, is_marked, mark, emit )
    else if is_let_exp E andalso is_let_exp Child then
      schema6a( E, is_marked, mark, emit )
    else if not(is_case_exp Child) then 
      ()
    else
    case Child of case_exp{exp=A,rules=Rules,exp_info=Exp_info} =>
    if not(#1 Exp_info orelse #1(get_exp_info E)) then
      ()
    else
    case E of
      app_exp{func,args,exp_info} =>
        emit(false,
          case_exp{exp=A, rules=
            let fun mk_rhs Rhs =
              if is_q_exp Rhs then
                set_q_exp_type(Rhs,#2 exp_info)
              else
                rename(
                  app_exp{func=func,args=list_replace(args,Arg_no,Rhs),
                    exp_info=mark exp_info},
                  false )
            in
              map(fn Rule as {pat,exp,...} => 
                mk_rule( Rule, pat, mk_rhs exp), 
                Rules)
            end,
            exp_info=mark'(Exp_info,exp_info)
            })
    | case_exp{exp,rules,exp_info} =>
      if Arg_no=0 then 
          (* Schema 4(a). *)
        emit( true,
          case_exp{ exp = A, rules =
            let
              fun mk_rhs Rhs =
                rename(
                  case_exp{ exp = Rhs, rules = rules, 
                    exp_info = mark exp_info },
                  false )
            in
              map( fn Rule as { pat, exp, ... } =>
                mk_rule( Rule, pat, mk_rhs exp ),
                Rules )
            end,
            exp_info = mark'( Exp_info, exp_info ) } )
      else
        emit( true,
          case_exp{exp=A,rules=
          let fun mk_rhs Rhs =
            rename(
              case_exp{exp=exp,rules=list_replace(rules,Arg_no-1,
                let 
                  val Rule = nth(rules,Arg_no-1)
                in
                  mk_rule( Rule, #pat Rule, Rhs)
                end ),
                exp_info=mark exp_info},
              false ) 
          in
            map(fn Rule as {pat,exp,...} => 
              mk_rule( Rule, pat, mk_rhs exp), 
              Rules)
          end,
          exp_info=mark'(Exp_info,exp_info) })
    | let_exp{ dec_list, exp, exp_info } =>
        emit( false,
          let fun mk_let E =
            if exists( fn{ func, ...} => sym_exp_member( func, E ), dec_list )
            then
              rename( let_exp{ dec_list=dec_list, exp=E, 
                  exp_info=mark(get_exp_info E)},
                false )
            else
              E
          in
            case_exp{ exp=mk_let A, exp_info=mark Exp_info,
              rules=map( fn Rule as {pat=P,exp=E,...} => 
                mk_rule( Rule, P, mk_let E), 
                Rules ) } 
          end )
  end (* fun move_case_outwards *)

fun move_case_outwards( Data : ( 'k, 'l )data, 
      E : (bool*'1a,'1b)e, Mark_enable :  bool,
      emit : bool * (bool*'1a,'1b)e -> unit ) : unit = 
  if (#time_out Data)() then () else
  case E of let_exp{dec_list,...} => (* Schemas 3a, 5a and 6a. *)
    move_case_outwards'( Data, E, length dec_list, Mark_enable, emit )
  | _ =>
  let val No_of_children =
    case E of
      app_exp{args,...} => length args
    | case_exp{rules,...} => 1+length rules
  in
    loop(fn Arg_no => move_case_outwards'( Data, E,Arg_no,Mark_enable,emit),
        fromto(0,No_of_children-1) )
  end


(* Examples.
  case A of Pat1 => f(Rhs1,B) | Pat2 => ?(Dont_know) | Pat3 => f(Rhs3,B) ->
  f( case A of Pat1 => Rhs1 | Pat2 => ?(Dont_know) | Pat3 => Rhs3, B )

case A of
  PatA1 => (case E of PatE1 => Rhs1 | PatE2 => Rhs2)
| PatA2 => (case E of PatE1 => Rhs1 | PatE2 => Rhs3)
->
case E of
  PatE1 => Rhs1
| PatE2 => case A of PatA1 => Rhs2 | PatA2 => Rhs3
*)



exception Move_case_inwards
exception Move_case_inwards_exn2
fun move_case_inwards(  Data : ( 'k, 'l )data, 
      E : (bool*'1a,'1b)e, Mark_enable : bool,
      emit : (bool*'1a,'1b)e->unit ) : unit =
  if (#time_out Data)() then () else
  let
    fun mark(Marked,Info) = if Mark_enable then (true,Info) else (Marked,Info)
    val Children = map( fn P => pos_to_sub( E, P ), children( [], E ) )
  in
  if exists( is_abstract_con_exp, Children ) then () else
  if is_app_exp E then
    schema5b( E, is_marked, mark, emit )
  else if is_let_exp E then
    schema6b( E, is_marked, mark, emit )
  else if not(is_case_exp E) then 
    raise Move_case_inwards_exn2
  else
  case E of case_exp{exp=A,rules=Rules,exp_info=Exp_info} =>
  let val Rhses = map(#exp,Rules)
  in
  if not(#1 Exp_info orelse 
         exists(fn Child => #1(get_exp_info Child), Rhses))
  then
    ()
  else
  let
    fun mark'((Marked,_),(_,Info)) = mark(Marked,Info)
    val Non_q_rhses = filter(fn Rhs => not(is_q_exp(Rhs:(bool*'1a,'1b)e)), Rhses)
    val Let_rhs_nos = filter( fn Arg_no => is_let_exp(nth(Rhses,Arg_no)),
                        fromto(0,length Rhses-1) )
  in
  if null Non_q_rhses then raise Move_case_inwards else
  if not(null Let_rhs_nos) then (* Schema 3b *)
    loop( fn Let_rhs_no =>
      let val let_exp{dec_list,exp,exp_info} = nth(Rhses,Let_rhs_no)
      in
        emit( let_exp{ dec_list=dec_list,
          exp=case_exp{ exp=A, rules=list_replace(Rules, Let_rhs_no,
            let
              val Rule = nth(Rules,Let_rhs_no)
            in
              mk_rule( Rule, #pat Rule, exp )
            end ),
                exp_info=mark Exp_info },
          exp_info=mark exp_info } )
      end,
      Let_rhs_nos )
  else (* Schema 1b or 2b *)
  case hd Non_q_rhses of
    app_exp{func,args,exp_info} =>
    let val Possible_arg_nos =
      if not(forall(fn app_exp{func=F, args=Args, ...} => 
                         F=func andalso length args = length Args 
                     | _ => false, 
                    tl  Non_q_rhses)) then
        nil
      else
        filter(fn Arg_no =>
          forall(fn app_exp{args=Args,...} => 
            exp_list_eq(delete_nth(Args,Arg_no), delete_nth(args,Arg_no)),
            tl Non_q_rhses),
          fromto(0,length args-1) )
        handle Delete_nth => (
          output( !std_err, "\nHERE 1\n" );
          raise Delete_nth
          )
    in
      map(fn Arg_no => (Arg_no,
        let 
          val Info = get_exp_info(nth(args,Arg_no))
          val Case_exp = case_exp{exp=A, rules=
          map(fn Rule as {pat,exp=E as app_exp{args,...},...} =>
            mk_rule( Rule, pat,
              if is_q_exp E then 
                set_q_exp_type(E,#2 Info) 
              else 
                nth(args,Arg_no)),
            Rules ),
          exp_info=mark'(Exp_info,Info) }
        in
          emit(
            app_exp{func=func, args=list_replace(args,Arg_no,Case_exp),
              exp_info=mark exp_info})
          
        end
        ),
        Possible_arg_nos );
      ()
    end
  | case_exp{exp,rules,exp_info} => (
  if not( forall( is_case_exp, Non_q_rhses ) ) then () else
  let
    val Rules' :: Ruless' = 
      map( fn case_exp{ rules, ... } => rules, Non_q_rhses )
  in
  if forall( fn Rs => rules_eq( Rules', Rs ), Ruless' ) then
    (* Apply schema 4(b). *)
    let
      val Info as ( _, Type ) = 
        case hd Non_q_rhses of
          case_exp{ exp, ... } => get_exp_info exp
      val Rhses = map( fn Rhs =>
        if is_q_exp Rhs then
          set_q_exp_type( Rhs, Type )
        else
          case Rhs of case_exp{ exp, ... } => exp,
        Rhses )
      val Case_E = case_exp{ exp = A,  rules =
        map( fn( Rule as { pat, ... }, Rhs ) => mk_rule( Rule, pat, Rhs ),
          combine( Rules, Rhses ) ),
        exp_info = mark Info }
    in
      emit(
        case_exp{ exp = Case_E, rules = Rules', exp_info = mark Exp_info }
        )
    end
  else
    ()
  end;

  let 
    val Possible_rhs_nos =
    if not(forall(fn case_exp{exp=E,...} => exp_eq(E,exp) | _ => false, Rhses))
    then
      nil
    else
      filter(fn Rhs_no =>
        forall(fn case_exp{rules=Rules,...} =>
          length Rules = length rules andalso
          let val Rules' = delete_nth(Rules,Rhs_no-1) 
              val rules'= delete_nth(rules,Rhs_no-1)
          in
            exp_list_eq(map(#pat,Rules'),map(#pat,rules')) andalso
            exp_list_eq(map(#exp,Rules'),map(#exp,rules'))
          end,
          Rhses),
        fromto(1,length rules) )
      handle Delete_nth => (
        output( !std_err, "\nHERE 2\n" );
        Print.print_exp' E;
        raise Delete_nth
        )
  in
    map(fn Rhs_no => 
      let val Case_exp = case_exp{exp=A, rules=
        map(fn Rule as {pat,exp=case_exp{rules,...},...} => 
            mk_rule( Rule, pat, #exp(nth(rules,Rhs_no-1))),
          Rules),
        exp_info=mark Exp_info }
      in
        emit(
          case_exp{exp=exp, rules=list_replace(rules,Rhs_no-1,
            let
              val Rule =nth(rules,Rhs_no-1)
            in
              mk_rule( Rule, #pat Rule, Case_exp)
            end ),
            exp_info=mark exp_info} )
      end,
      Possible_rhs_nos);
    ()
  end )
  | let_exp{...} => raise Move_case_inwards
  end
  end
  end (* fun move_case_inwards *)




fun find_children( Data : ( 'k, 'l )data, 
      E : (bool*'1a,'1b)e, Mark_enable : bool,
      emit : bool*(bool*'1a,'1b)e -> unit ) : unit = 
  if (#time_out Data)() then () else
  (
  move_case_outwards( Data, E, Mark_enable, emit );
  move_case_inwards( Data, E, Mark_enable, fn New_E => emit(false,New_E) );
  let fun try( Sub, build : (bool*'1a,'1b)e -> (bool*'1a,'1b)e ) : unit =
    find_children( Data, Sub, Mark_enable, fn(Dead_code_elim,New_Sub) =>
      emit(Dead_code_elim,build New_Sub) )
  in
  case E of
    app_exp{func,args,exp_info} =>
      loop(fn Arg_no => try(nth(args,Arg_no),fn New_arg =>
        app_exp{func=func, args=list_replace(args,Arg_no,New_arg),
          exp_info=exp_info}),
        fromto(0,length args-1) )
  | case_exp{exp,rules,exp_info} =>
      loop(fn Rule_no => 
        let val Rule as {pat,exp=Rhs,...} = 
         nth(rules,Rule_no) 
        in
        try(Rhs,fn New_Rhs =>
          case_exp{exp=exp,
            rules=list_replace(rules,Rule_no,
              mk_rule( Rule, pat, New_Rhs )),
            exp_info=exp_info})
        end,
        fromto(0,length rules-1) )
  | let_exp{dec_list,exp,exp_info} => 
      (
      try(exp,fn New_exp => 
        let_exp{dec_list=dec_list,exp=New_exp,exp_info=exp_info});
      loop(fn Dec_no =>
        let val {func,pat,exp=Rhs,dec_info} = nth(dec_list,Dec_no)
        in
          try(Rhs,fn New_Rhs =>
            let_exp{dec_list=list_replace(dec_list,Dec_no,
                {func=func,pat=pat,exp=New_Rhs,dec_info=dec_info}),
              exp=exp,
              exp_info=exp_info})
        end,
        fromto(0,length dec_list-1) )
      )
  end
 )



(* Test declarations: *)


(*

val E = parse_exp"\
\      case Ys of \
\        nil => Ys \
\      | (Y1 :: Ys1) => \
\      case Xs of nil => Xs | (X1 :: Xs1) => ?( Dont_know ) \
\"


val E1 = parse_exp "g(f(case A of Pat1 => ?(Dont_know) | Pat2 => Rhs2,B))"

val E2 = parse_exp"\
\  case LeXs of \
\    bt_nil => RiXs \
\  | bt_cons(RoLeXs,LeLeXs,RiLeXs) => \
\  case LeRiXs of \
\    bt_nil => bt_cons(RoRiXs,LeXs,RiRiXs) \
\  | bt_cons(RoLeRiXs,LeLeRiXs,RiLeRiXs) => \
\      bt_cons(RoRiXs,LeXs,LeLeXs) \
\"

fun test(E,Pos) =
  let fun emit(Dead_code_elim,New_E) =
    (
    output(!std_out,"\n\nDead_code_elim = "^Bool.toString Dead_code_elim);
    output(!std_out,"\nNew_E =\n");
    print_exp(from_marked New_E);
    output(!std_out,"\nMarked positions =");
    print_list(print_int_list,marked_poses New_E)
    )
    val E = mark_exp_at_pos(to_marked E,Pos)
  in
    find_children(E,true,emit)
  end

*)
   



(* 
Compound case-dists are produced by iteratively deepening the number of
"moves". Fingerprints in a hash table are used to avoid duplication.
For a given exp produced through a compound case-dist, the hash table
entry is (Fingerprint,(No_of_moves,Found)) where Found=true iff the exp has
been produced earlier during the current iteration.
The function iteration is called with Move_count_limit=1,2,3,... and
emits exps produced with exactly Move_count_limit moves.
*)

local

exception Case_dist_exn

fun iterate( 
      get_exp_info : bool * '1a -> exp_info_type, 
      get_dec_info : '1b -> dec_info_type, 
      Data : ( bool * '1a, '1b )data,
      D as {func,pat,exp,dec_info} : (bool*'1a,'1b)d, Move_count, 
      Move_count_limit, emit : (bool*'1a,'1b)e -> unit ) : unit =
  if (#time_out Data)() then () else
(* Assumes that D isn't a "duplicate". *)
  if Move_count = Move_count_limit then (
(*
    p"\nemitting in iterate:\n";
    print_hash_table Data;
    nl();
*)
    emit exp
    )
  else
    let 
      fun to_exp E = info_map( get_exp_info, get_dec_info, E )

      fun emit'( Dead_code_elim, New_exp : ( bool * '1a, '1b )e ) =
      if not( scope_check( New_exp, func::nil, vars_in_pat pat ) ) then
        ()
      else if not( (#size_check Data) New_exp ) then
        ()
      else
      let
        val New_exp = remove_all_q_case_exps New_exp
        val New_D : ( bool * '1a, '1b )d = 
          { func=func, pat=pat, exp=New_exp, dec_info=dec_info }
        val () = type_check_dec_raise{
          func = func, pat = to_exp pat, exp = to_exp New_exp,
          dec_info = get_dec_info dec_info }
        val New_D = 
          if Dead_code_elim then dead_code_elim' New_D else New_D
        val Fingerprint = Evaluate.syntactic_fingerprint New_D
      in
      case H.find (#table Data) Fingerprint of
        NONE => 
          if H.numItems (#table Data) > 10 * Constants.Total_max_REQ_storage 
          then
            ()
          else ( 
          H.insert (#table Data) ( Fingerprint, ( Move_count+1, ref true ) );
          iterate( get_exp_info, get_dec_info, Data, New_D, Move_count+1, Move_count_limit, emit )
          )
      | SOME(No_of_moves,Found) =>
          if Move_count+1=No_of_moves andalso not( !Found ) then (
            H.remove (#table Data) Fingerprint;
            H.insert (#table Data) ( Fingerprint, ( Move_count+1, ref true ) );
            iterate( get_exp_info, get_dec_info, Data, New_D, Move_count+1, Move_count_limit, emit )
            )
          else
            ()
      end
    in
      find_children( Data, exp, true, emit' )
    end (* fun iterate *)

in (* local *)

fun initial_hash_table( D : ('1a,'1b)d ) =
  let
    val Table : ( int * bool ref )H.hash_table = 
      H.mkTable( 1000, Case_dist_exn )
  in
    H.insert Table ( Evaluate.syntactic_fingerprint D, ( 0, ref true ) );
    Table
  end
  

fun iteration( get_exp_info, get_dec_info, Data,
      D as {func,pat,exp,dec_info} : ('1a,'1b)d, Move_count_limit : int, 
      top_pos_ok : pos -> bool, emit :  ('1a,'1b)d * pos list -> unit ) : unit =
  if (#time_out Data)() then () else
  let 
    val exp = remove_all_q_case_exps(to_marked exp)
    val get_exp_info = fn( _, Info ) => get_exp_info Info
    val All_poses = 
      filter( top_pos_ok, all_poses_in_preorder exp )
    val pat = to_marked pat
    val () =
      H.appi ( fn( _, ( _, Found ) ) => Found := false  )(#table Data)
  in
    loop( fn Pos => iterate( get_exp_info, get_dec_info, Data,
        { func = func, pat = pat, exp = mark_exp_at_pos( exp, Pos ),
          dec_info = dec_info} : ( bool * '1a, '1b )d,
        0,
        Move_count_limit,
        fn New_exp => emit( { func = func, pat = from_marked pat,
            exp = from_marked New_exp, dec_info = dec_info} : ('1a,'1b)d,
          marked_poses New_exp)),
      All_poses )
  end


(* Test declarations: *)


(*
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
\        g1(sort(Xs1)) \
\      end \
\" )

fun test N = map(fn Move_count_limit =>
  let fun emit(D,Active_poses) = (
    nl();nl();
    print_list(print_int_list,Active_poses);
    nl();
    print_dec' D;
    nl()
    )
  in
    iteration( get_exp_info, get_dec_info,D,Move_count_limit,fn _ => true,emit)
  end,
  fromto(1,N) )
      

*)
end (* local *)

open Int_dyn

fun dry_search( get_exp_info, get_dec_info, 
      Data, D : ('1a,'1b)d, top_pos_ok : pos->bool ) 
    : int * array =
(* Returns (Max_move_count_limit,Class_cardinalities). *)
  let
    val Class_cardinalities = array(50,0)
    val Max_move_count_limit = ref 0
    val Emitted = ref true
    fun emit(New_D,_) = (
      update( Class_cardinalities, !Max_move_count_limit,
        sub( Class_cardinalities, !Max_move_count_limit)+1 );
      Emitted := true
      )
    fun run() = if not(!Emitted) then () else (
      Emitted := false;
      inc Max_move_count_limit;
      iteration( get_exp_info, get_dec_info, Data, D, !Max_move_count_limit, top_pos_ok, emit );
      run()
      )
  in
    run();
    (!Max_move_count_limit - 1, Class_cardinalities)
  end
   
fun cost_comp( Cost_limit : real, Max_move_count_limit : int, 
      Class_cards : array ) : int * ( int -> real option ) =
  let
    val Cum_class_cards = array(50,0)
    fun cum_cards I = 
      if I>Max_move_count_limit then () else (
        update(Cum_class_cards, I, 
          sub(Cum_class_cards,I-1)+sub(Class_cards,I));
        cum_cards(I+1)
        )
    val _ = cum_cards 1
    val Interval_widths = Real_dyn.array(50,0.0)
    fun interval_widths(I,So_far) =
      if I>Max_move_count_limit then () else 
      let val Width = 
        So_far+real(sub(Class_cards,I))/real(sub(Cum_class_cards,I))
      in
        Real_dyn.update(Interval_widths,I,Width);
        interval_widths(I+1,Width)
      end
        
     val _ = interval_widths(1,0.0)   
         
    fun find_limit I =
      if I<=0 then (0, fn _ => NONE) else
      let val Max_cost = 
        real(sub(Cum_class_cards,I))*Real_dyn.sub(Interval_widths,I)
      in
        if Max_cost>Cost_limit then
          find_limit(I-1)
        else
          ( I, 
            fn N => 
              if N > I then 
                NONE
              else
                SOME( real( sub( Cum_class_cards, N ) ) * 
                      Real_dyn.sub( Interval_widths, I ) ) )
      end
  in
    find_limit Max_move_count_limit
  end (* fun cost_comp *)

(*
The returned function pos_transform maps a position before CASE-DIST to the
corresponding position(s) after CASE-DIST. It is implemented by labeling each
expression tree node with its original position before applying CASE-DIST. 
After the CASE-DIST, the new tree is traveresed and the old-to-new position 
mapping is stored in a hash table. If old and new are the same, they are not 
stored.
*)

fun CASE_DIST_trfs( 
      get_exp_info : '1a -> exp_info_type,
      get_dec_info : '1b -> dec_info_type,
      (* The two functions above are needed to enable type checking. *)
      D : ('1a,'1b)d, 
      Cost_limits : real list, 
      REQ_cost_limit : real,
      top_pos_ok : pos->bool, 
      emit : ('1a,'1b)d * atomic_trf_record list * real option list -> unit 
      ) : unit =
  let
    val D = pre_process D
    val get_exp_info = fn( _, Info ) => get_exp_info Info
    val T = mk_timer "CASE_DIST_trfs"
    val Max_size = 100 + 10 * exp_size( #exp D )
    val Max_time = 0.4*REQ_cost_limit*synt_and_eval_time_per_exp()

    val Data = {
      time_out = fn() => check_timer T > Max_time,
      table = initial_hash_table D,
      size_check = fn E => exp_size E < Max_size
      }

    val _ = start_timer T
    val ( Max_move_count_limit, Class_cards ) =
      dry_search( get_exp_info, get_dec_info, Data, D, top_pos_ok )

    val Xs = map( fn Cost_limit => 
      cost_comp( Cost_limit, Max_move_count_limit, Class_cards ),
      Cost_limits )

    val Max_move_count_limit : int = max( op<, map( #1, Xs ) )

    val Cost_comps : ( int -> real option ) list = map( #2, Xs )

    val Data = {
      time_out = fn() => false,
      table = initial_hash_table D,
      size_check = fn E => exp_size E < Max_size
      }

  in
    loop(fn Move_count_limit =>
      let 
        fun emit'( New_D, Active_poses ) =
          case post_process New_D of ( New_D, pos_transform ) =>
          emit( 
            New_D, 
            [ CASE_DIST{ activated_poses = Active_poses, 
                pos_transform = pos_transform } ],
            map( fn cost_comp => cost_comp Move_count_limit, Cost_comps ) )
      in
        iteration( get_exp_info, get_dec_info, 
          Data, D, Move_count_limit, top_pos_ok, emit' )
      end,
      fromto( 1, Max_move_count_limit )
      );
    delete_timer T
  end
  handle Ex => (
    output(!std_out,"\n\nD = \n");
    print_dec' D;
    output(!std_out,"\nCost_limits = " ); print_real_list Cost_limits;
    output(!std_out,"\nREQ_cost_limit = "^Real.toString REQ_cost_limit);
    re_raise(Ex,"CASE_DIST_TRFS")
    )



end (* structure Case_dist *)
