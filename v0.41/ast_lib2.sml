(* File: ast_lib2.sml.
   Created: 1998-06-30.
   Modified: 1999-11-15
*)


structure Ast_lib2 :
sig

val remove_as : 
  ( 'a, 'b )Ast.e -> ( 'a, 'b )Ast.e

val find_as_subst : 
  ( 'a, 'b )Ast.e -> ( 'a, 'b )Ast_lib.exp_subst

val pos_to_pat_subst' : 
  bool * bool * ( 'a, 'b )Ast.d * Ast_lib.pos -> ( 'a, 'b )Ast_lib.exp_subst

structure FIFO_occurrence_checking :
  sig

type '1a data = 
  ( '1a * '1a -> order ) * int * real Queue.queue * 
  '1a Lib.Real_HashTable.hash_table

val new : ( '1a * '1a -> order ) * int -> '1a data

val insert : real * '1a * '1a data -> '1a option

val contents : '1a data -> '1a list

  end

datatype abstr_kind = abstre | rec_arg_type_exists | other_abstr

val abstr_kind_to_string : abstr_kind -> string

type CSE_record = { 
  case_pos : Ast_lib.pos, 
  common_poses_before : Ast_lib.pos list,
  v_poses : Ast_lib.pos list 
  }

val CSE_pos_transform : Ast_lib.pos * CSE_record -> Ast_lib.pos
val CSE_pos_transform_list : Ast_lib.pos * CSE_record list -> Ast_lib.pos

val print_CSE_record : CSE_record -> unit
val print_CSE_record_list : CSE_record list -> unit


type r_top_poses = Ast_lib.pos list * ( Ast.exp * Ast_lib.pos ) option


type R_record = { 
  r_top_poses : r_top_poses, 
  bottom_poses : Ast_lib.pos list, 
  bottom_labels : Ast.exp list,
  synted_exp : Ast.exp,
  not_activated_syms : Ast.symbol list }
 
val Dummy_R_record : R_record

val print_R_record : R_record -> unit

type REQ_record = R_record

val Dummy_REQ_record : REQ_record

val print_REQ_record : REQ_record -> unit


type simple_R_record = {
  top_pos : Ast_lib.pos,
  rel_bottom_poses : Ast_lib.pos list,
  synted_exp : Ast.exp,
  synted_exp_bottom_poses : Ast_lib.pos list
  }

val simple_R_record_eq : simple_R_record * simple_R_record -> bool
val print_simple_R_record : simple_R_record -> unit
val print_simple_R_record_list : simple_R_record list -> unit
val set_top_pos : simple_R_record * Ast_lib.pos -> simple_R_record

val top_and_bottoms : simple_R_record -> Ast_lib.pos * Ast_lib.pos list

val from_REQ_record : REQ_record -> simple_R_record list
val from_R_record : R_record -> simple_R_record list

val apply_simple_R_record : Ast.dec * simple_R_record -> Ast.dec

val apply_cses :
      ( Ast.dec * Ast_lib.pos list -> Ast.dec * CSE_record list ) * 
      Ast.dec *  
      CSE_record list *  
      simple_R_record list *  
      Ast_lib.pos list list
      ->
      Ast.dec * CSE_record list * simple_R_record list


val synted_exp_match : Ast.exp * Ast_lib.pos list * simple_R_record list -> bool

val emit_rename : 
      simple_R_record list * Ast.dec -> simple_R_record list * Ast.dec

val apply_R_record :
      ( Ast.dec * Ast_lib.pos list -> Ast.dec * CSE_record list ) * 
      Ast.dec * R_record 
      -> 
      Ast.dec * CSE_record list

type Simple_R_and_CSE_records = {
  just_before_cse : simple_R_record list,
  cse_records : CSE_record list,
  after_cse : simple_R_record list }

val print_Simple_R_and_CSE_records : Simple_R_and_CSE_records -> unit

type so_far = simple_R_record list * Ast.dec * 
              ( Ast_lib.pos -> Ast_lib.pos ) * simple_R_record list
(* ( Original records, D so far, pos transform so far, 
     Maintained records ) 

The last component is used to guide common subexpression elimination and
renaming done before emission.

This type is manipulated by req_lib5.sml
*)
val print_so_far : so_far -> unit

datatype atomic_trf_record =
  ABSTR of { 
    let_exp_pos : Ast_lib.pos,
    func : Ast.symbol,
    parameters_added : Ast.exp list,
    abstr_kind : abstr_kind
    }
| REQ of REQ_record list * Simple_R_and_CSE_records
| MULTIR of { so_far : so_far, original_r_records : R_record list,
    new_min_once : Ast.symbol list list, 
    top_pos_ok' : Ast_lib.pos list -> bool,
    poses_ok' : ( Ast_lib.pos * Ast_lib.pos list )list -> bool
    }
| BLASTABLE_MULTIR of R_record list
| DUPL of { top_pos : Ast_lib.pos, synted_exp : Ast.exp,
            selected_rhs_poses : Ast_lib.pos list }
| R of R_record * CSE_record list
| CASE_DIST of { activated_poses : Ast_lib.pos list,
                 pos_transform : Ast_lib.pos -> Ast_lib.pos list }
| BLASTABLE_CASE_DIST of Ast_lib.pos list
| EMB of { let_exp_pos : Ast_lib.pos , min_once : Ast.symbol list list}
| match_errors of Ast.symbol list



val make_blastable : atomic_trf_record -> atomic_trf_record
val unmake_blastable : atomic_trf_record -> atomic_trf_record

val print_atomic_trf_record : atomic_trf_record -> unit
val print_trf_history : atomic_trf_record list -> unit

val occurring_syms : ( 'a, 'b )Ast.e -> Ast_lib.Symbol_set.set
val pat_syms : ( 'a, 'b )Ast.e -> Ast_lib.Symbol_set.set

(* Functions used by DUPL: *)
val selected_rhs_poses : ('a,'b)Ast.e -> Ast_lib.pos list
val other_rhs_poses : ('a,'b)Ast.e -> Ast_lib.pos list
end =
struct
open Lib List1 Ast Ast_lib Ast_lib3 Ast_lib6


fun find_as_subst( Pat : ('a,'b)e ) : ('a,'b)exp_subst =
  case Pat of
    app_exp{ func, args, ... } => flat_map( find_as_subst, args )
  | as_exp{ var, pat, exp_info } =>
      case find_as_subst pat of Subst =>
        ( app_exp{ func = var, args = nil, exp_info = exp_info },
          apply_exp_subst( remove_as pat, Subst ) ) :: Subst


local

fun pos_to_pat_subst_d( 
      Ignore_var_case_rule : bool,
      Require_var_pat : bool,
      So_far : ('a,'b)exp_subst, 
      D as { pat, exp, ... } : ('a,'b)d,
      Pos : pos ) : ( 'a, 'b )exp_subst =
  pos_to_pat_subst_e( Ignore_var_case_rule, Require_var_pat,
    find_as_subst pat @ So_far, exp, Pos )

and pos_to_pat_subst_e( _, _, So_far, E, [] ) = So_far
  | pos_to_pat_subst_e( Ignore_var_case_rule, Require_var_pat, 
       So_far, E, P1 :: Ps1 ) =
let
  fun s E = pos_to_pat_subst_e( Ignore_var_case_rule, Require_var_pat, 
              So_far, E, Ps1 )
in
  case E of
    app_exp{ args, ... } => s( nth( args, P1 ) )
  | case_exp{ exp, rules, ... } => 
      if P1 = 0 then
        s exp
      else
      let
        val { pat, exp = RHS, ... } = nth( rules, P1 - 1 )
        val As_subst = find_as_subst pat
        val New = 
          if is_variable_exp pat then
            ( pat, apply_exp_subst( exp, So_far ) )
          else
            ( exp, apply_exp_subst( remove_as pat, As_subst ) )
        val So_far =
          As_subst @ (
          if is_variable_exp pat andalso Ignore_var_case_rule orelse
             Require_var_pat andalso null( var_exps_in_pat pat )
          then
            So_far
          else
            exp_subst_compose( So_far, [ New ] ) )
      in
        pos_to_pat_subst_e( Ignore_var_case_rule, Require_var_pat, 
          So_far, RHS, Ps1 )
      end
  | let_exp{ dec_list, exp, ... } =>
      if P1 < length dec_list then
        pos_to_pat_subst_d( Ignore_var_case_rule, Require_var_pat, 
          So_far, nth( dec_list, P1 ), Ps1 )
      else
        s exp
end (* pos_to_pat_subst_e *)

in (* local *)

fun pos_to_pat_subst'( Ignore_var_case_rule, Require_var_pat, D, Pos ) = 
  pos_to_pat_subst_d( Ignore_var_case_rule, Require_var_pat, [], D, Pos )

end (* local *)


structure FIFO_occurrence_checking =
struct

structure Q = Queue
structure H = Real_HashTable

type '1a data = 
  ( '1a * '1a -> order ) * int * real Q.queue * '1a H.hash_table

exception FIFO_occurrence_checking_exn1 

fun new( cmp : '1a * '1a -> order, Max_card : int ) : '1a data =
  ( cmp, Max_card, Q.mkQueue(),
    H.mkTable( Max_card, FIFO_occurrence_checking_exn1 ) )

fun insert( Fingerprint : real, X : '1a,
      ( cmp, Max_card, Queue, T ) : '1a data ) : '1a option =
  case H.find T Fingerprint of
    SOME X' => (
      case cmp( X, X' ) of
        LESS => (
          H.remove T Fingerprint;
          H.insert T ( Fingerprint, X );
          NONE 
          )
      | _ => NONE
      )
  | NONE => (
      Q.enqueue( Queue, Fingerprint );
      H.insert T ( Fingerprint, X );
      (
      if Q.length Queue > Max_card then 
        let 
          val F = Q.dequeue Queue
          val Y = H.lookup T F
        in
          H.remove T F;
          SOME Y
        end
      else
        NONE ) )

fun contents( ( cmp, Max_card, Queue, T ) : '1a data ) : '1a list =
  map( fn Fingerprint => H.lookup T Fingerprint, Q.contents Queue )
          

end (* structure FIFO_occurrence_checking *)


datatype abstr_kind = abstre | rec_arg_type_exists | other_abstr

fun abstr_kind_to_string( X : abstr_kind ) : string =
  case X of
    abstre => "abstre"
  | rec_arg_type_exists => "rec_arg_type_exists"
  | other_abstr => "other_abstr"


type CSE_record = { 
  case_pos : pos, 
  common_poses_before : pos list,
  v_poses : pos list 
  }


fun CSE_pos_transform( Pos : pos,
      { case_pos, common_poses_before, ... } : CSE_record
      ) : pos =
  if not( is_prefix( case_pos, Pos ) ) then
    Pos
  else
  case filter( fn Common_pos => is_prefix( Common_pos, Pos ),
         common_poses_before )
  of
    [] => case_pos @ [1] @ drop( length case_pos, Pos )
  | [ Common_pos ] => case_pos @ [0] @ drop( length Common_pos, Pos )

fun CSE_pos_transform_list( Pos, Xs : CSE_record list ) : pos =
  case Xs of
    nil => Pos
  | X :: Xs => CSE_pos_transform_list( CSE_pos_transform( Pos, X ), Xs )

  
fun print_CSE_record( { case_pos, common_poses_before, v_poses } ) : unit = (
  p"\ncase_pos = "; print_pos case_pos;
  p"\ncommon_poses_before = "; print_pos_list common_poses_before;
  p"\nv_poses = "; print_pos_list v_poses;
  nl() )

fun print_CSE_record_list( Xs : CSE_record list) : unit = (
  p"\nCSE_record:\n";
  loop( print_CSE_record, Xs ) )


type r_top_poses = pos list * ( exp * pos ) option
(* Consider for example ( Alt, SOME( Stand_in, Pos ) ) : r_top_poses.
   If length Alt >= 2, the R is substitutive.
   Stand_in is derived from patterns using pos_to_pat_subst and is a semantics
   preserving substitute for each of the exps given by the poses in Alt.
   Pos is a local position within Stand_in.
   A bottom pos is relative to the exp to be replaced within Stand_in, not
   to Stand_in 
*)

type R_record = { 
  r_top_poses : r_top_poses, 
  bottom_poses : pos list, 
  bottom_labels : exp list,
  synted_exp : exp,
  not_activated_syms : symbol list }

val Dummy_R_record : R_record = {
  r_top_poses = ( [], NONE ),
  bottom_poses = [],
  bottom_labels = [],
  synted_exp = Ast.Dummy_exp,
  not_activated_syms = [] }


type REQ_record = R_record
val Dummy_REQ_record : REQ_record = Dummy_R_record


fun print_R_record{ r_top_poses, bottom_poses, bottom_labels, synted_exp, 
       not_activated_syms } = (
  case r_top_poses of ( Alt, Stand_in_opt ) => (
    p "\n  Top poses = [ ";
    loop( fn P => ( print_pos P; p " " ), Alt );
    p" ] ";
    case Stand_in_opt of
      NONE => ()
    | SOME( Stand_in, Pos ) => (
        p "\n    Stand-in = "; Print.print_exp' Stand_in;
        p "\n    Local pos within stand-in = "; print_pos Pos
        ) );
  p "\n  Bottom poses = [ ";
  loop( fn Pos => (output(!std_out,"  ");print_pos Pos),
       bottom_poses ); 
  p " ] ";
  p "\n  Bottom labels =";
  loop( fn X => ( p " "; Print.print_exp' X ), bottom_labels );
  p "\n  Synted exp = "; Print.print_exp' synted_exp;
  p "\n  Not activated symbols = ";
  print_list(fn Sym => 
    output(!std_out,symbol_to_string Sym), 
    not_activated_syms)
  )


val print_REQ_record = print_R_record


type simple_R_record = {
  top_pos : pos,
  rel_bottom_poses : pos list,
  synted_exp : exp,
  synted_exp_bottom_poses : pos list
  }

fun simple_R_record_eq( R1 : simple_R_record, R2 : simple_R_record ) : bool =
  #top_pos R1 = #top_pos R2 andalso
  #rel_bottom_poses R1 = #rel_bottom_poses R2 andalso
  exp_eq( #synted_exp R1, #synted_exp R2 ) andalso
  #synted_exp_bottom_poses R1 = #synted_exp_bottom_poses R2



fun print_simple_R_record{ top_pos, rel_bottom_poses, synted_exp, 
       synted_exp_bottom_poses } = (
  p "\n  Top pos = "; print_pos top_pos;
  p "\n  Relative bottom poses = "; print_pos_list rel_bottom_poses;
  p "\n  Synted exp = "; Print.print_exp' synted_exp;
  p "\n Synted exp bottom poses = "; print_pos_list synted_exp_bottom_poses
  )

fun print_simple_R_record_list Xs = 
  loop( fn Record => ( print_simple_R_record Record; nl() ), Xs )


fun set_top_pos( { top_pos, rel_bottom_poses, synted_exp, 
       synted_exp_bottom_poses } : simple_R_record,
       Top_pos : pos ) = {
  top_pos = Top_pos,
  rel_bottom_poses = rel_bottom_poses,
  synted_exp = synted_exp,
  synted_exp_bottom_poses = synted_exp_bottom_poses }



exception From_req_record_exn
fun from_REQ_record( Record as {
      r_top_poses = ( Alt, Stand_in_opt ),
      bottom_poses,
      bottom_labels,
      synted_exp,
      ...
      } : REQ_record 
      ) : simple_R_record list =
case Alt of [] => [] | _::_ =>
let
  val ( bottom_poses, synted_exp ) =
    case Stand_in_opt of
      NONE => ( bottom_poses, synted_exp )
    | SOME( Stand_in, Pos ) => 
        ( map( fn Bottom_pos => Pos @ Bottom_pos, bottom_poses ),
          pos_replace( Stand_in, Pos, fn _ => synted_exp ) )

(* Check validity of bottom_poses: *)
  val _ =
    case Stand_in_opt of
      NONE => ()
    | SOME( Stand_in, Pos ) => 
    loop( fn( Bottom_pos, Label ) =>
      if type_of_exp( pos_to_sub( Stand_in, Bottom_pos ) ) <>
         type_of_exp Label
      then
        raise From_req_record_exn
      else
        (),
      combine( bottom_poses, bottom_labels ) )

  fun pos_of_exp E =
    case all_poses_filter( fn Sub => exp_eq( Sub, E ), synted_exp ) of
      [ Pos] => Pos
  handle Ex => (
    p"\npos_of_exp: E = "; Print.print_exp' E;
    raise Ex )
in
  map( fn Top_pos => {
    top_pos = Top_pos,
    rel_bottom_poses = bottom_poses,
    synted_exp = synted_exp,
    synted_exp_bottom_poses = map( pos_of_exp, bottom_labels )
    },
    Alt )
end (* fun from_REQ_record *)
handle Ex => (
  p"\nfrom_REQ_record: Record =\n";
  print_REQ_record Record;
  raise Ex )

val from_R_record = from_REQ_record

(* One R_record may be translated into several simple_R_record values *)

fun top_and_bottoms( 
      { top_pos, synted_exp_bottom_poses, ... } : simple_R_record
      ) : pos * pos list =
  (
    top_pos,
    map( fn Synted_exp_bottom_pos => top_pos @ Synted_exp_bottom_pos,
      synted_exp_bottom_poses ) )


exception Apply_simple_R_record
fun apply_simple_R_record( 
      D as { exp, ... } : dec,
      Record as {
        top_pos,
        rel_bottom_poses,
        synted_exp,
        synted_exp_bottom_poses } : simple_R_record
      ) : dec =
  if length rel_bottom_poses <> length synted_exp_bottom_poses then
    raise Apply_simple_R_record
  else
let
  val Sub = pos_to_sub( exp, top_pos )
  val Bottoms = map( fn Pos => pos_to_sub( Sub, Pos ), rel_bottom_poses )
  fun g( [], E ) = E
    | g( ( Bottom, Pos ) :: Bottoms_and_poses, E ) =
        g( Bottoms_and_poses, pos_replace( E, Pos, fn _ => Bottom ) )
  val synted_exp = g( combine( Bottoms, synted_exp_bottom_poses ), synted_exp )
in
  pos_replace_dec( D, top_pos, fn _ => synted_exp )
end




structure S = Symbol_set

fun occurring_syms( E : ( 'a, 'b )e ) : S.set =
let
  val Syms = S.empty()
  fun ins Sym = S.insert( Sym, Syms )
  fun s( app_exp{ func, args, ... } ) = ( ins func; loop( s, args ) )
    | s( case_exp{ exp, rules, ... } ) = ( 
        s exp;
        loop( fn { exp, ... } => s exp, rules )
        )
    | s( let_exp{ dec_list, exp, ... } ) = (
        s exp;
        loop( fn { exp, ... } => s exp, dec_list )
        )
in
  s E;
  Syms
end
    
fun pat_syms( E : ( 'a, 'b )e ) : S.set =
(* E is not a pat!. *)
let
  val Syms = S.empty()
  fun ins Sym = S.insert( Sym, Syms )
  fun s( In, app_exp{ func, args, ... } ) = 
        ( if In then ins func else (); loop( fn A => s( In, A ), args ) )
    | s( false, case_exp{ exp, rules, ... } ) = ( 
        s( false, exp );
        loop( fn{ pat, exp, ... } => ( s( true, pat ); s( false, exp ) ), 
          rules )
        )
    | s( false, let_exp{ dec_list, exp, ... } ) = (
        s( false, exp );
        loop( fn { pat, exp, ... } => ( s( true, pat ); s( false, exp ) ), 
          dec_list )
        )
    | s( true, as_exp{ var, pat, ... } ) = ( ins var; s( true, pat ) )
in
  s( false, E );
  Syms
end
    
     



(* The following function is only used for checking/verifying that the
   top poses of all applied simple R records are properly maintained.
   It checks that the synted exp in a given record actually matches the
   exp Sub that occurs at a "maintained" top pos.
*)
local

fun synted_exp_match'( Synted_exp : exp, Sub : exp, 
            Bottom_labels : symbol list ) : bool =
  (
  case Synted_exp of
    app_exp{ func, args = nil, ... } => member( func, Bottom_labels )
  | _ => false 
  )
  orelse
  (
  case ( Synted_exp, Sub ) of
    ( app_exp{ func, args, ... }, app_exp{ func = F, args = Args, ... } ) =>
      func = F andalso
      forall( fn( A1, A2 ) => synted_exp_match'( A1, A2, Bottom_labels ),
        combine( args, Args ) )
  | ( case_exp{ exp, rules, ... }, case_exp{ exp = E, rules = Rules, ... } ) =>
      synted_exp_match'( exp, E, Bottom_labels ) andalso
      forall( fn( { exp = RHS1, ... }, { exp = RHS2, ... } ) =>
        synted_exp_match'( RHS1, RHS2, Bottom_labels ),
        combine( rules, Rules ) )
  | ( _, _ ) => false
  )


in (* local *)

exception Match_exn

fun synted_exp_match( E : exp, Top_poses : pos list, Records : simple_R_record list ) 
    : bool =
  if length Top_poses <> length Records then
    raise Match_exn
  else
    forall( fn( Top_pos, { synted_exp, synted_exp_bottom_poses, ... } ) => 
      let
        val Bottom_labels = 
          map( fn Pos => 
            case pos_to_sub( synted_exp, Pos ) of
              app_exp{ func, args=nil, ... } => func,
            synted_exp_bottom_poses )
      in
        synted_exp_match'( synted_exp, pos_to_sub( E, Top_pos ), Bottom_labels )
      end,
      combine( Top_poses, Records ) )

end (* local *)



val Invalid_pos = [ Max_int ]

fun apply_cses(
      cse : dec * pos list -> dec * CSE_record list,
      D_so_far : dec,
      CSE_records_so_far : CSE_record list,
      Maintained : simple_R_record list,
      Common_poses_list : pos list list
      ) : dec * CSE_record list * simple_R_record list =
(* Assumes that Common_poses_list is sorted so that the corresponding 
   common exps are in order of decreasing size. *)
let
  val Common_poses_list : pos list list =
    filter( fn Xs => length Xs >= 2,
      map( pos_hash_make_set, Common_poses_list ) )
in
  case Common_poses_list of
    [] => ( D_so_far, CSE_records_so_far, 
            make_set'( simple_R_record_eq, Maintained ) )
  | Common_poses :: Common_poses_list =>
let
  val ( D_so_far, CSE_records ) = cse( D_so_far, Common_poses )
  
  fun pt( Pos : pos ) : pos = CSE_pos_transform_list( Pos, CSE_records )
  fun pts( Poses : pos list ) : pos list = map( pt, Poses )
  
  val CSE_records_so_far = CSE_records @
    map( fn{ case_pos, common_poses_before, v_poses } =>
      { case_pos = pt case_pos,
        common_poses_before = [ Invalid_pos ],
        v_poses = pts v_poses },
      CSE_records_so_far )

  val Maintained = 
  (* May contain duplicates after executing the following code. *)
    map( fn Simple => set_top_pos( Simple, pt( #top_pos Simple ) ),
      Maintained )

  val Common_poses_list : pos list list = map( pts, Common_poses_list )
in
  apply_cses( cse, D_so_far, CSE_records_so_far, Maintained, 
    Common_poses_list )
end
end (* fun apply_cses *)

local

structure H = Symbol_HashTable

exception Rename_synted_exp
fun rename_synted_exp( 
      D as { exp, ... } : dec,
      Record as {
        top_pos,
        rel_bottom_poses,
        synted_exp,
        synted_exp_bottom_poses } : simple_R_record
      ) : dec * simple_R_record * sym_subst =
  if length rel_bottom_poses <> length synted_exp_bottom_poses then
    raise Rename_synted_exp
  else
let
  val Sub = pos_to_sub( exp, top_pos )
  val Bottoms = map( fn Pos => pos_to_sub( Sub, Pos ), synted_exp_bottom_poses )
  fun g( [], E ) = E
    | g( ( Bottom, Pos ) :: Bottoms_and_poses, E ) =
        g( Bottoms_and_poses, pos_replace( E, Pos, fn _ => Bottom ) )
  val ( synted_exp, Subst ) = reversible_rename synted_exp
  val Sub = g( combine( Bottoms, synted_exp_bottom_poses ), synted_exp )
in
  ( pos_replace_dec( D, top_pos, fn _ => Sub ),
    { top_pos = top_pos, rel_bottom_poses = rel_bottom_poses,
      synted_exp = synted_exp, 
      synted_exp_bottom_poses = synted_exp_bottom_poses },
    H.map (fn [Sym] => Sym) (symbol_hash_table_reverse Subst) )
end (* fun rename_synted_exp *)

fun rename_simple( New : simple_R_record, Subst : sym_subst,
                   Old : simple_R_record )
    : simple_R_record =
  if not( is_prefix( #top_pos New, #top_pos Old ) ) then Old else {
    top_pos = #top_pos Old,
    rel_bottom_poses = #rel_bottom_poses Old,
    synted_exp = apply_sym_subst_exp( #synted_exp Old, Subst ),
    synted_exp_bottom_poses = #synted_exp_bottom_poses Old }

in (* local   *)


exception Emit_rename_exn
fun emit_rename( 
      Records_so_far : simple_R_record list, 
      Remaining_records : simple_R_record list, 
      Remaining_records' : simple_R_record list, 
      D_so_far 
      ) : simple_R_record list * dec =
  case ( Remaining_records, Remaining_records' ) of
    ( [], [] ) => ( Records_so_far, D_so_far )
  | ( Remaining :: Remaining_records, Remaining' :: Remaining_records' ) =>
  if not( synted_exp_match( #exp D_so_far, 
            [ #top_pos Remaining ], [ Remaining' ] ) )
  then
    raise Emit_rename_exn
  else
  let
    val ( D_so_far, Remaining, Subst ) = 
      rename_synted_exp( D_so_far, Remaining )
    fun rs Old = rename_simple( Remaining, Subst, Old )
    fun m Xs = map( rs, Xs )
  in
    emit_rename( Remaining :: m Records_so_far, m Remaining_records, 
      Remaining_records', D_so_far )
  end

fun prerequisite( X : ('a,'b)e, Y : ('a,'b)e ) : bool =
  not( null( filter( is_variable,
    Symbol_set.set_to_list( 
      Symbol_set.intersection( pat_syms X, occurring_syms Y ) ) ) ) )

fun build_dag( less : 'a * 'a -> bool, Xs : ( 'a * int )list )
    : ( int * int )list =
  map( fn ( (_,N1), (_,N2) ) => (N1,N2),
    filter( fn( (X1,N1), (X2,N2) ) => N1<>N2 andalso less(X1,X2), 
      cart_prod( Xs, Xs ) ) )

fun root( Xs : ( int * int )list, Unchosen : int list ) : int =
let
  val Root :: _ =
    filter( fn U => not( exists( fn( _, To ) => To = U, Xs ) ), Unchosen )
in
  Root
end

fun topsort( Xs : ( int * int ) list, Unchosen : int list ) : int list =
  if null Unchosen then
    []
  else
    case root( Xs, Unchosen ) of Root =>
      Root :: 
      topsort( filter( fn( From, To ) => From <> Root andalso To <> Root, Xs ),
               filter( fn U => U<> Root, Unchosen ) )

val emit_rename = fn ( Records, D ) => 
let
  fun less( X : simple_R_record, Y : simple_R_record ) =
    is_prefix( #top_pos X, #top_pos Y ) andalso
    prerequisite( #synted_exp X, #synted_exp Y )

  val Indexed_records = indexize( Records, 0 )

  val DAG = build_dag( less, Indexed_records )
(*
  val () = (
    nl(); 
    print_list( fn(X,Y) => 
      ( p"("; print_int X; p","; print_int Y; p")" ),
      DAG );
    nl() )
*)
  val Is : int list = topsort( DAG, map( #2, Indexed_records ) )

  fun g( [], [] ) = []
    | g( I :: Is, Indexed_records ) =
    case pfilter( fn( _, I' ) => I=I', Indexed_records ) of 
      ( [ ( Record, _ ) ], Indexed_records ) =>
        Record :: g( Is, Indexed_records )

  val Records = g( Is, Indexed_records )
in
  emit_rename( [], Records, Records, D )
end (* val emit_rename *)
handle Ex => (
  p"\nemit_rename:\n";
  print_simple_R_record_list Records; nl();
  Print.print_dec' D; nl();
  raise Ex )

end (* local *)



fun apply_R_record( cse : dec * pos list -> dec * CSE_record list,
      D : dec, Record : R_record ) : dec * CSE_record list =
let
  val Rs = from_R_record Record
  fun g [] = D
    | g( X :: Xs ) = apply_simple_R_record( g Xs, X )
  val D = g Rs
  val ( D, CSE_records, Rs ) =
    apply_cses( cse, D, [], Rs, [ #1( #r_top_poses Record ) ] )

  val ( _, D ) = emit_rename( Rs, D )
  
in
  ( D, CSE_records )
end


type Simple_R_and_CSE_records = {
  just_before_cse : simple_R_record list,
  cse_records : CSE_record list,
  after_cse : simple_R_record list }

fun print_Simple_R_and_CSE_records( 
      { just_before_cse, cse_records, after_cse } : Simple_R_and_CSE_records
      ) : unit = (
  p"\njust_before_cse =\n ";
  print_simple_R_record_list just_before_cse;
  p"\ncse_records = \n";
  print_CSE_record_list cse_records;
  p"\nafter_cse =\n ";
  print_simple_R_record_list after_cse;
  nl() )
  

type so_far = simple_R_record list * Ast.dec * 
              ( Ast_lib.pos -> Ast_lib.pos ) * simple_R_record list

fun print_so_far( Original, D_so_far, _, Maintained ) = (
  p"\noriginal =\n"; print_simple_R_record_list Original;
  p"\nd_so_far =\n"; Print.print_dec' D_so_far;
  p"\nmaintained =\n"; print_simple_R_record_list Maintained;
  nl() )

datatype atomic_trf_record =
  ABSTR of { 
    let_exp_pos : pos,
    func : symbol,
    parameters_added : exp list,
    abstr_kind : abstr_kind
    }
| REQ of REQ_record list * Simple_R_and_CSE_records
| MULTIR of { so_far : so_far, original_r_records : R_record list,
    new_min_once : symbol list list, 
    top_pos_ok' : pos list -> bool,
    poses_ok' : ( pos * pos list )list -> bool
    }
| BLASTABLE_MULTIR of R_record list
| DUPL of { top_pos : Ast_lib.pos, synted_exp : Ast.exp,
            selected_rhs_poses : Ast_lib.pos list }
| R of R_record * CSE_record list
| CASE_DIST of { activated_poses : pos list,
                 pos_transform : pos -> pos list }
| BLASTABLE_CASE_DIST of pos list
| EMB of { let_exp_pos : pos , min_once : symbol list list}
| match_errors of Ast.symbol list

fun make_blastable( Record : atomic_trf_record ) : atomic_trf_record =
  case Record of
    CASE_DIST{ activated_poses, ... } =>
      BLASTABLE_CASE_DIST activated_poses
  | MULTIR{ original_r_records, ... } =>
      BLASTABLE_MULTIR original_r_records
  | X => X




fun unmake_blastable( Record : atomic_trf_record ) : atomic_trf_record =
  case Record of
    BLASTABLE_CASE_DIST activated_poses =>
      CASE_DIST{ 
        activated_poses = activated_poses, pos_transform = fn _ => [] }
  | BLASTABLE_MULTIR original_r_records =>
      MULTIR{ so_far = ( [], Dummy_dec, fn [] => [], [] ),
        original_r_records = original_r_records,
        new_min_once = [],
        top_pos_ok' = fn [] => true,
        poses_ok' = fn [] => true }
  | X => X

fun print_atomic_trf_record( Record ) =
  case unmake_blastable Record of
    ABSTR{ let_exp_pos, func, parameters_added, abstr_kind } => (
      p "\nABSTR "; print_pos let_exp_pos;
      p( "\n" ^ symbol_to_string func ^ "  : " );
      loop( fn E => ( Print.print_exp' E; p " " ), parameters_added );
      p( "\n" ^ abstr_kind_to_string abstr_kind )
      )
  | REQ( REQ_records, Simple_R_and_CSE_records ) =>
      ( output(!std_out,"\nREQ "); 
        loop( fn Record => ( nl(); print_R_record Record ), REQ_records ) )
(*
        nl();
        print_Simple_R_and_CSE_records Simple_R_and_CSE_records )
*)
  | MULTIR{ so_far, original_r_records, new_min_once : symbol list list, 
            ...  } => (
      p"\nMULTIR:\n";
    (*  p"\nso_far = \n"; print_so_far so_far; *)
      p"\noriginal_r_records = \n"; 
      loop( fn Record => ( print_R_record Record; nl() ), original_r_records );
      p"\nnew_min_once = ";
      print_list( fn Syms => 
        print_list( fn Sym => output(!std_out,symbol_to_string Sym), Syms ),
        new_min_once ); nl() 
      )

  | DUPL{ top_pos, synted_exp, selected_rhs_poses } => (
      p "\nDUPL "; print_pos top_pos;
      p"\n"; Print.print_exp' synted_exp;
      nl(); print_pos_list selected_rhs_poses 
      )

  | R( R_record, CSE_record ) => ( 
      output(!std_out,"\nR "); 
      print_R_record R_record; nl() )
(*
      print_CSE_record_list CSE_record )
*)

  | CASE_DIST{ activated_poses, ... } =>
      ( output(!std_out,"\nCASE-DIST");
        map( fn Pos => (output(!std_out,"  ");print_pos Pos),
             activated_poses ); ()
        )
  | EMB{let_exp_pos,min_once} =>      
      ( output(!std_out,"\nEMB "); print_pos let_exp_pos;
        print_list(fn Syms => print_list(fn Sym => 
          output( !std_out, symbol_to_string Sym ), Syms ),
          min_once) )


fun print_trf_history( Trf_history : atomic_trf_record list ) =
  loop( print_atomic_trf_record,Trf_history)

     
(* Code related to the DUPL transformation: *)
     
exception Selected_rhs_poses_exn
fun selected_rhs_poses( E ) : pos list =
let
  val Selected = flat_map( fn Pos =>
    case pos_to_sub( E, Pos ) of
      case_exp{ rules, ... } =>
        if not( exists( fn{ exp, ... } => is_case_exp exp, rules ) ) then
          map( fn( _, I ) => snoc( Pos, I ), indexize( rules, 1 ) )
        else
          []
   | _ => [],
   all_poses_in_preorder E )

  val Parent :: Parents = map( lt, Selected )
  val  () = 
    if forall( fn X => X = Parent, Parents ) then 
      () 
    else 
      raise Selected_rhs_poses_exn
in
  Selected
end

fun other_rhs_poses( E ) : pos list =
  flat_map( fn Pos =>
    case pos_to_sub( E, Pos ) of
      case_exp{ rules, ... } =>
        if exists( fn{ exp, ... } => is_case_exp exp, rules ) then
          flat_map( fn( { exp, ... }, I ) => 
            if is_case_exp exp then
              []
            else
              [ snoc( Pos, I ) ],
    
            indexize( rules, 1 ) )
        else
          []
   | _ => [],
   all_poses_in_preorder E )










end (* structure Ast_lib2 *)
