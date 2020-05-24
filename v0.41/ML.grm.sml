functor MLLrValsFun (structure Token : TOKEN) : ML_LRVALS = 
struct
structure ParserData=
struct
structure Header = 
struct
(* File: ML.grm 
   Created: 1993-05-26
   Modified: 1996-06-02
*)



end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\206\000\003\000\206\000\004\000\206\000\005\000\206\000\
\\007\000\206\000\008\000\206\000\010\000\206\000\013\000\206\000\
\\014\000\206\000\017\000\206\000\018\000\206\000\021\000\085\000\
\\022\000\084\000\023\000\083\000\024\000\082\000\027\000\081\000\
\\028\000\080\000\030\000\206\000\034\000\206\000\000\000\
\\001\000\001\000\207\000\003\000\207\000\004\000\207\000\005\000\207\000\
\\007\000\207\000\008\000\207\000\010\000\207\000\013\000\207\000\
\\014\000\207\000\017\000\207\000\018\000\207\000\021\000\085\000\
\\022\000\084\000\023\000\083\000\024\000\082\000\027\000\081\000\
\\028\000\080\000\030\000\207\000\034\000\207\000\000\000\
\\001\000\001\000\011\000\000\000\
\\001\000\001\000\011\000\003\000\010\000\004\000\009\000\030\000\008\000\000\000\
\\001\000\006\000\065\000\009\000\064\000\012\000\063\000\029\000\062\000\
\\031\000\061\000\032\000\060\000\033\000\059\000\000\000\
\\001\000\007\000\123\000\000\000\
\\001\000\008\000\140\000\018\000\088\000\019\000\087\000\020\000\086\000\
\\021\000\085\000\022\000\084\000\023\000\083\000\024\000\082\000\
\\027\000\081\000\028\000\080\000\000\000\
\\001\000\010\000\122\000\018\000\088\000\019\000\087\000\020\000\086\000\
\\021\000\085\000\022\000\084\000\023\000\083\000\024\000\082\000\
\\027\000\081\000\028\000\080\000\000\000\
\\001\000\012\000\034\000\033\000\033\000\000\000\
\\001\000\012\000\047\000\033\000\033\000\000\000\
\\001\000\012\000\053\000\025\000\016\000\033\000\052\000\000\000\
\\001\000\013\000\037\000\000\000\
\\001\000\013\000\071\000\017\000\070\000\026\000\069\000\027\000\041\000\000\000\
\\001\000\013\000\071\000\017\000\070\000\027\000\041\000\000\000\
\\001\000\013\000\097\000\000\000\
\\001\000\013\000\104\000\000\000\
\\001\000\013\000\106\000\016\000\075\000\017\000\105\000\000\000\
\\001\000\013\000\121\000\017\000\120\000\018\000\088\000\019\000\087\000\
\\020\000\086\000\021\000\085\000\022\000\084\000\023\000\083\000\
\\024\000\082\000\027\000\081\000\028\000\080\000\000\000\
\\001\000\013\000\125\000\016\000\075\000\000\000\
\\001\000\013\000\126\000\000\000\
\\001\000\013\000\130\000\000\000\
\\001\000\013\000\138\000\000\000\
\\001\000\015\000\139\000\027\000\041\000\000\000\
\\001\000\016\000\075\000\019\000\143\000\000\000\
\\001\000\019\000\035\000\000\000\
\\001\000\019\000\038\000\000\000\
\\001\000\019\000\042\000\027\000\041\000\000\000\
\\001\000\026\000\136\000\000\000\
\\001\000\033\000\013\000\000\000\
\\001\000\033\000\023\000\000\000\
\\001\000\033\000\025\000\000\000\
\\001\000\033\000\027\000\000\000\
\\001\000\033\000\029\000\000\000\
\\001\000\033\000\056\000\000\000\
\\001\000\033\000\093\000\000\000\
\\001\000\033\000\127\000\000\000\
\\001\000\034\000\000\000\000\000\
\\148\000\000\000\
\\149\000\000\000\
\\150\000\000\000\
\\151\000\000\000\
\\152\000\001\000\011\000\003\000\010\000\004\000\009\000\030\000\008\000\000\000\
\\153\000\000\000\
\\154\000\000\000\
\\155\000\000\000\
\\156\000\005\000\030\000\000\000\
\\157\000\000\000\
\\158\000\000\000\
\\159\000\000\000\
\\160\000\000\000\
\\161\000\000\000\
\\162\000\017\000\026\000\000\000\
\\163\000\012\000\017\000\025\000\016\000\000\000\
\\164\000\000\000\
\\165\000\014\000\078\000\000\000\
\\166\000\016\000\075\000\000\000\
\\167\000\010\000\079\000\000\000\
\\168\000\016\000\075\000\000\000\
\\169\000\000\000\
\\170\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\000\000\
\\174\000\016\000\075\000\017\000\105\000\000\000\
\\175\000\000\000\
\\176\000\022\000\074\000\033\000\073\000\000\000\
\\177\000\000\000\
\\178\000\022\000\074\000\033\000\073\000\000\000\
\\179\000\000\000\
\\180\000\016\000\075\000\000\000\
\\181\000\000\000\
\\182\000\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\023\000\083\000\024\000\082\000\027\000\081\000\
\\028\000\080\000\000\000\
\\183\000\018\000\088\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\023\000\083\000\024\000\082\000\027\000\081\000\
\\028\000\080\000\000\000\
\\184\000\005\000\031\000\000\000\
\\185\000\000\000\
\\186\000\000\000\
\\187\000\000\000\
\\188\000\027\000\041\000\000\000\
\\189\000\000\000\
\\190\000\027\000\041\000\000\000\
\\191\000\000\000\
\\192\000\011\000\045\000\012\000\044\000\033\000\043\000\000\000\
\\193\000\017\000\098\000\027\000\041\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\000\000\
\\197\000\000\000\
\\198\000\000\000\
\\199\000\000\000\
\\200\000\000\000\
\\201\000\000\000\
\\202\000\012\000\092\000\031\000\091\000\032\000\090\000\033\000\089\000\000\000\
\\203\000\000\000\
\\204\000\000\000\
\\205\000\019\000\087\000\020\000\086\000\021\000\085\000\022\000\084\000\
\\023\000\083\000\024\000\082\000\027\000\081\000\028\000\080\000\000\000\
\\208\000\000\000\
\\209\000\000\000\
\\210\000\022\000\084\000\023\000\083\000\000\000\
\\211\000\022\000\084\000\023\000\083\000\000\000\
\\212\000\021\000\085\000\022\000\084\000\023\000\083\000\024\000\082\000\
\\027\000\081\000\028\000\080\000\000\000\
\\213\000\021\000\085\000\022\000\084\000\023\000\083\000\024\000\082\000\
\\027\000\081\000\028\000\080\000\000\000\
\\214\000\000\000\
\\215\000\000\000\
\\216\000\017\000\131\000\018\000\088\000\019\000\087\000\020\000\086\000\
\\021\000\085\000\022\000\084\000\023\000\083\000\024\000\082\000\
\\027\000\081\000\028\000\080\000\000\000\
\\217\000\000\000\
\\218\000\014\000\144\000\019\000\087\000\020\000\086\000\021\000\085\000\
\\022\000\084\000\023\000\083\000\024\000\082\000\027\000\081\000\
\\028\000\080\000\000\000\
\\219\000\000\000\
\"
val actionRowNumbers =
"\003\000\038\000\039\000\040\000\
\\041\000\037\000\028\000\052\000\
\\052\000\029\000\043\000\003\000\
\\030\000\051\000\031\000\052\000\
\\032\000\045\000\044\000\073\000\
\\070\000\008\000\042\000\024\000\
\\052\000\048\000\011\000\025\000\
\\052\000\029\000\026\000\081\000\
\\009\000\010\000\050\000\049\000\
\\033\000\046\000\074\000\009\000\
\\004\000\080\000\009\000\009\000\
\\012\000\009\000\068\000\067\000\
\\057\000\058\000\059\000\010\000\
\\054\000\047\000\056\000\077\000\
\\071\000\091\000\093\000\092\000\
\\034\000\004\000\004\000\002\000\
\\014\000\082\000\079\000\010\000\
\\009\000\075\000\013\000\062\000\
\\010\000\010\000\015\000\016\000\
\\033\000\010\000\004\000\004\000\
\\004\000\004\000\004\000\004\000\
\\004\000\004\000\004\000\088\000\
\\090\000\089\000\004\000\084\000\
\\017\000\007\000\005\000\078\000\
\\009\000\018\000\019\000\066\000\
\\065\000\069\000\035\000\010\000\
\\060\000\053\000\055\000\100\000\
\\099\000\098\000\096\000\095\000\
\\097\000\001\000\000\000\094\000\
\\020\000\103\000\004\000\085\000\
\\009\000\004\000\083\000\027\000\
\\076\000\061\000\064\000\063\000\
\\087\000\004\000\021\000\101\000\
\\022\000\006\000\010\000\104\000\
\\086\000\004\000\102\000\023\000\
\\105\000\004\000\009\000\072\000\
\\106\000\036\000"
val gotoT =
"\
\\001\000\145\000\002\000\005\000\003\000\004\000\004\000\003\000\
\\011\000\002\000\016\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\010\000\003\000\004\000\004\000\003\000\011\000\002\000\
\\016\000\001\000\000\000\
\\000\000\
\\000\000\
\\007\000\013\000\008\000\012\000\000\000\
\\005\000\018\000\006\000\017\000\007\000\013\000\008\000\016\000\000\000\
\\017\000\020\000\018\000\019\000\000\000\
\\000\000\
\\002\000\022\000\003\000\004\000\004\000\003\000\011\000\002\000\
\\016\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\013\000\008\000\026\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\014\000\030\000\000\000\
\\000\000\
\\000\000\
\\007\000\013\000\008\000\034\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\037\000\006\000\017\000\007\000\013\000\008\000\016\000\000\000\
\\017\000\038\000\018\000\019\000\000\000\
\\000\000\
\\000\000\
\\014\000\044\000\000\000\
\\007\000\049\000\021\000\048\000\022\000\047\000\023\000\046\000\000\000\
\\000\000\
\\000\000\
\\009\000\053\000\010\000\052\000\000\000\
\\000\000\
\\000\000\
\\014\000\055\000\000\000\
\\012\000\056\000\000\000\
\\000\000\
\\014\000\065\000\015\000\064\000\000\000\
\\014\000\066\000\000\000\
\\000\000\
\\014\000\070\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\049\000\021\000\075\000\022\000\047\000\023\000\046\000\
\\024\000\074\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\092\000\000\000\
\\012\000\093\000\000\000\
\\016\000\094\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\049\000\021\000\097\000\022\000\047\000\023\000\046\000\000\000\
\\014\000\065\000\015\000\098\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\049\000\022\000\100\000\023\000\099\000\000\000\
\\007\000\049\000\021\000\101\000\022\000\047\000\023\000\046\000\000\000\
\\000\000\
\\000\000\
\\009\000\105\000\010\000\052\000\000\000\
\\007\000\049\000\021\000\106\000\022\000\047\000\023\000\046\000\000\000\
\\012\000\107\000\000\000\
\\012\000\108\000\000\000\
\\012\000\109\000\000\000\
\\012\000\110\000\000\000\
\\012\000\111\000\000\000\
\\012\000\112\000\000\000\
\\012\000\113\000\000\000\
\\012\000\114\000\000\000\
\\012\000\115\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\117\000\013\000\116\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\014\000\065\000\015\000\122\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\049\000\021\000\127\000\022\000\047\000\023\000\046\000\
\\024\000\126\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\117\000\013\000\130\000\000\000\
\\000\000\
\\014\000\132\000\020\000\131\000\000\000\
\\012\000\133\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\117\000\013\000\135\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\049\000\021\000\139\000\022\000\047\000\023\000\046\000\000\000\
\\000\000\
\\000\000\
\\012\000\140\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\143\000\000\000\
\\014\000\132\000\020\000\144\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 146
val numrules = 72
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | ID of  (string)
 | REAL of  (real) | INT of  (int) | TY_EXP_LIST of  (Ast.ty_exp list)
 | CART_PROD of  (Ast.ty_exp list) | BASIC_TY_EXP of  (Ast.ty_exp)
 | TY_EXP of  (Ast.ty_exp)
 | RULE_LIST of  ( ( Ast.exp_info_type, Ast.dec_info_type )  Ast.rule_type list)
 | RULE of  ({ pat:Ast.pat,exp:Ast.exp } ) | FUN_DEC of  (Ast.dec)
 | FUN_DECS of  (Ast.dec list) | FUN_DEC_LIST of  (Ast.dec list)
 | PAT_LIST of  (Ast.pat list) | PAT of  (Ast.pat)
 | EXP_LIST of  (Ast.exp list) | EXP of  (Ast.exp)
 | TYPE_DEC of  ({ ty_con:Ast.symbol,ty_pars:Ast.ty_var list,ty_exp:Ast.ty_exp } )
 | ALT of  ({ constr:Ast.symbol,domain:Ast.ty_exp option } )
 | ALT_LIST of  ({ constr:Ast.symbol,domain:Ast.ty_exp option }  list)
 | TY_PAR_LIST of  (Ast.symbol list) | TY_VAR of  (Ast.symbol)
 | DATATYPE_DEC of  (Ast.datatype_dec)
 | DATATYPE_DECS of  (Ast.datatype_dec list)
 | DATATYPE_DEC_LIST of  (Ast.datatype_dec list)
 | DEC of  (Ast.parse_result) | DEC_LIST of  (Ast.parse_result list)
 | START of  (Ast.parse_result list)
end
type svalue = MlyValue.svalue
type result = Ast.parse_result list
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change = 
nil
val noShift = 
fn (T 33) => true | _ => false
val showTerminal =
fn (T 0) => "FUN"
  | (T 1) => "VAL"
  | (T 2) => "DATATYPE"
  | (T 3) => "TYPE"
  | (T 4) => "AND"
  | (T 5) => "LET"
  | (T 6) => "IN"
  | (T 7) => "END"
  | (T 8) => "CASE"
  | (T 9) => "OF"
  | (T 10) => "AS"
  | (T 11) => "LPAR"
  | (T 12) => "RPAR"
  | (T 13) => "VBAR"
  | (T 14) => "ARROW"
  | (T 15) => "THIN_ARROW"
  | (T 16) => "COMMA"
  | (T 17) => "SEMICOLON"
  | (T 18) => "EQ"
  | (T 19) => "LESS'"
  | (T 20) => "PLUS"
  | (T 21) => "MUL"
  | (T 22) => "DIV"
  | (T 23) => "MINUS"
  | (T 24) => "PRIME"
  | (T 25) => "COLON"
  | (T 26) => "CONS"
  | (T 27) => "APPEND"
  | (T 28) => "RAISE"
  | (T 29) => "EXCEPTION"
  | (T 30) => "INT"
  | (T 31) => "REAL"
  | (T 32) => "ID"
  | (T 33) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13)
 :: (T 14) :: (T 15) :: (T 16) :: (T 17) :: (T 18) :: (T 19) :: (T 20)
 :: (T 21) :: (T 22) :: (T 23) :: (T 24) :: (T 25) :: (T 26) :: (T 27)
 :: (T 28) :: (T 29) :: (T 33) :: nil
end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.DEC_LIST DEC_LIST,DEC_LIST1left,DEC_LIST1right))::
rest671) => let val result=MlyValue.START(( DEC_LIST ))
 in (LrTable.NT 0,(result,DEC_LIST1left,DEC_LIST1right),rest671) end
| (1,(_,(MlyValue.FUN_DEC_LIST FUN_DEC_LIST,FUN_DEC_LIST1left,
FUN_DEC_LIST1right))::rest671) => let val result=MlyValue.DEC((
 Ast.parsed_fun FUN_DEC_LIST ))
 in (LrTable.NT 2,(result,FUN_DEC_LIST1left,FUN_DEC_LIST1right),
rest671) end
| (2,(_,(MlyValue.TYPE_DEC TYPE_DEC,TYPE_DEC1left,TYPE_DEC1right))::
rest671) => let val result=MlyValue.DEC(( Ast.parsed_type TYPE_DEC ))
 in (LrTable.NT 2,(result,TYPE_DEC1left,TYPE_DEC1right),rest671) end
| (3,(_,(MlyValue.DATATYPE_DEC_LIST DATATYPE_DEC_LIST,
DATATYPE_DEC_LIST1left,DATATYPE_DEC_LIST1right))::rest671) => let val 
result=MlyValue.DEC(( Ast.parsed_datatype DATATYPE_DEC_LIST ))
 in (LrTable.NT 2,(result,DATATYPE_DEC_LIST1left,
DATATYPE_DEC_LIST1right),rest671) end
| (4,(_,(MlyValue.DEC DEC,DEC1left,DEC1right))::rest671) => let val 
result=MlyValue.DEC_LIST(( DEC::nil ))
 in (LrTable.NT 1,(result,DEC1left,DEC1right),rest671) end
| (5,(_,(MlyValue.DEC_LIST DEC_LIST,_,DEC_LIST1right))::_::(_,(_,
EXCEPTION1left,_))::rest671) => let val result=MlyValue.DEC_LIST((
 DEC_LIST ))
 in (LrTable.NT 1,(result,EXCEPTION1left,DEC_LIST1right),rest671) end
| (6,(_,(MlyValue.DEC_LIST DEC_LIST,_,DEC_LIST1right))::(_,(
MlyValue.DEC DEC,DEC1left,_))::rest671) => let val result=
MlyValue.DEC_LIST(( DEC::DEC_LIST ))
 in (LrTable.NT 1,(result,DEC1left,DEC_LIST1right),rest671) end
| (7,(_,(MlyValue.DATATYPE_DECS DATATYPE_DECS,_,DATATYPE_DECS1right))
::(_,(_,DATATYPE1left,_))::rest671) => let val result=
MlyValue.DATATYPE_DEC_LIST(( DATATYPE_DECS ))
 in (LrTable.NT 3,(result,DATATYPE1left,DATATYPE_DECS1right),rest671)
 end
| (8,(_,(MlyValue.DATATYPE_DEC DATATYPE_DEC,DATATYPE_DEC1left,
DATATYPE_DEC1right))::rest671) => let val result=
MlyValue.DATATYPE_DECS(( DATATYPE_DEC :: nil ))
 in (LrTable.NT 4,(result,DATATYPE_DEC1left,DATATYPE_DEC1right),
rest671) end
| (9,(_,(MlyValue.DATATYPE_DECS DATATYPE_DECS,_,DATATYPE_DECS1right))
::_::(_,(MlyValue.DATATYPE_DEC DATATYPE_DEC,DATATYPE_DEC1left,_))::
rest671) => let val result=MlyValue.DATATYPE_DECS((
 DATATYPE_DEC :: DATATYPE_DECS ))
 in (LrTable.NT 4,(result,DATATYPE_DEC1left,DATATYPE_DECS1right),
rest671) end
| (10,(_,(MlyValue.ALT_LIST ALT_LIST,_,ALT_LIST1right))::_::(_,(
MlyValue.ID ID,_,_))::(_,(MlyValue.TY_PAR_LIST TY_PAR_LIST,
TY_PAR_LIST1left,_))::rest671) => let val result=MlyValue.DATATYPE_DEC
((
 {
      ty_con = Ast.string_to_symbol(Ast.ty_con_sym,ID),
      ty_pars = TY_PAR_LIST,
      alts = ALT_LIST
      } 
))
 in (LrTable.NT 5,(result,TY_PAR_LIST1left,ALT_LIST1right),rest671)
 end
| (11,(_,(MlyValue.ID ID,_,ID1right))::(_,(_,PRIME1left,_))::rest671)
 => let val result=MlyValue.TY_VAR((
 Ast.string_to_symbol( Ast.ty_var_sym, "'" ^ ID ) ))
 in (LrTable.NT 6,(result,PRIME1left,ID1right),rest671) end
| (12,(_,(_,_,RPAR1right))::(_,(MlyValue.TY_PAR_LIST TY_PAR_LIST,_,_))
::(_,(_,LPAR1left,_))::rest671) => let val result=MlyValue.TY_PAR_LIST
(( TY_PAR_LIST ))
 in (LrTable.NT 7,(result,LPAR1left,RPAR1right),rest671) end
| (13,(_,(MlyValue.TY_PAR_LIST TY_PAR_LIST,_,TY_PAR_LIST1right))::_::(
_,(MlyValue.TY_VAR TY_VAR,TY_VAR1left,_))::rest671) => let val result=
MlyValue.TY_PAR_LIST(( TY_VAR :: TY_PAR_LIST ))
 in (LrTable.NT 7,(result,TY_VAR1left,TY_PAR_LIST1right),rest671) end
| (14,(_,(MlyValue.TY_VAR TY_VAR,TY_VAR1left,TY_VAR1right))::rest671)
 => let val result=MlyValue.TY_PAR_LIST(( TY_VAR :: nil ))
 in (LrTable.NT 7,(result,TY_VAR1left,TY_VAR1right),rest671) end
| (15,rest671) => let val result=MlyValue.TY_PAR_LIST(( nil ))
 in (LrTable.NT 7,(result,defaultPos,defaultPos),rest671) end
| (16,(_,(MlyValue.ALT_LIST ALT_LIST,_,ALT_LIST1right))::_::(_,(
MlyValue.ALT ALT,ALT1left,_))::rest671) => let val result=
MlyValue.ALT_LIST(( ALT :: ALT_LIST ))
 in (LrTable.NT 8,(result,ALT1left,ALT_LIST1right),rest671) end
| (17,(_,(MlyValue.ALT ALT,ALT1left,ALT1right))::rest671) => let val 
result=MlyValue.ALT_LIST(( ALT :: nil ))
 in (LrTable.NT 8,(result,ALT1left,ALT1right),rest671) end
| (18,(_,(MlyValue.TY_EXP TY_EXP,_,TY_EXP1right))::_::(_,(MlyValue.ID 
ID,ID1left,_))::rest671) => let val result=MlyValue.ALT((
 { 
      constr = Ast.string_to_symbol( Ast.func_sym, ID ),
      domain = SOME TY_EXP
      } 
))
 in (LrTable.NT 9,(result,ID1left,TY_EXP1right),rest671) end
| (19,(_,(MlyValue.ID ID,ID1left,ID1right))::rest671) => let val 
result=MlyValue.ALT((
 { 
      constr = Ast.string_to_symbol( Ast.func_sym, ID ), 
      domain = NONE 
      } 
))
 in (LrTable.NT 9,(result,ID1left,ID1right),rest671) end
| (20,(_,(MlyValue.TY_EXP TY_EXP,_,TY_EXP1right))::_::(_,(MlyValue.ID 
ID,_,_))::(_,(MlyValue.TY_PAR_LIST TY_PAR_LIST,_,_))::(_,(_,TYPE1left,
_))::rest671) => let val result=MlyValue.TYPE_DEC((
 {
      ty_con = Ast.string_to_symbol( Ast.ty_con_sym, ID ),
      ty_pars = TY_PAR_LIST,
      ty_exp = TY_EXP
      } 
))
 in (LrTable.NT 10,(result,TYPE1left,TY_EXP1right),rest671) end
| (21,(_,(MlyValue.TY_VAR TY_VAR,TY_VAR1left,TY_VAR1right))::rest671)
 => let val result=MlyValue.BASIC_TY_EXP(( Ast.ty_var_exp TY_VAR ))
 in (LrTable.NT 21,(result,TY_VAR1left,TY_VAR1right),rest671) end
| (22,(_,(MlyValue.ID ID,ID1left,ID1right))::rest671) => let val 
result=MlyValue.BASIC_TY_EXP((
 
      Ast.ty_con_exp(
        Ast.string_to_symbol( Ast.ty_con_sym, ID ),
        nil) 
      
))
 in (LrTable.NT 21,(result,ID1left,ID1right),rest671) end
| (23,(_,(_,_,RPAR1right))::(_,(MlyValue.TY_EXP TY_EXP,_,_))::(_,(_,
LPAR1left,_))::rest671) => let val result=MlyValue.BASIC_TY_EXP((
 TY_EXP ))
 in (LrTable.NT 21,(result,LPAR1left,RPAR1right),rest671) end
| (24,(_,(MlyValue.ID ID,_,ID1right))::_::(_,(MlyValue.TY_EXP_LIST 
TY_EXP_LIST,_,_))::(_,(_,LPAR1left,_))::rest671) => let val result=
MlyValue.BASIC_TY_EXP((
 
      Ast.ty_con_exp( 
        Ast.string_to_symbol( Ast.ty_con_sym, ID ), 
        TY_EXP_LIST ) 
      
))
 in (LrTable.NT 21,(result,LPAR1left,ID1right),rest671) end
| (25,(_,(MlyValue.ID ID,_,ID1right))::(_,(MlyValue.BASIC_TY_EXP 
BASIC_TY_EXP,BASIC_TY_EXP1left,_))::rest671) => let val result=
MlyValue.BASIC_TY_EXP((
 
      Ast.ty_con_exp( 
        Ast.string_to_symbol( Ast.ty_con_sym, ID ), 
        BASIC_TY_EXP::nil ) 
      
))
 in (LrTable.NT 21,(result,BASIC_TY_EXP1left,ID1right),rest671) end
| (26,(_,(MlyValue.TY_EXP TY_EXP2,_,TY_EXP2right))::_::(_,(
MlyValue.TY_EXP TY_EXP1,TY_EXP1left,_))::rest671) => let val result=
MlyValue.TY_EXP_LIST(( TY_EXP1::TY_EXP2::nil ))
 in (LrTable.NT 23,(result,TY_EXP1left,TY_EXP2right),rest671) end
| (27,(_,(MlyValue.TY_EXP_LIST TY_EXP_LIST,_,TY_EXP_LIST1right))::_::(
_,(MlyValue.TY_EXP TY_EXP,TY_EXP1left,_))::rest671) => let val result=
MlyValue.TY_EXP_LIST(( TY_EXP::TY_EXP_LIST ))
 in (LrTable.NT 23,(result,TY_EXP1left,TY_EXP_LIST1right),rest671) end
| (28,(_,(MlyValue.BASIC_TY_EXP BASIC_TY_EXP2,_,BASIC_TY_EXP2right))::
_::(_,(MlyValue.BASIC_TY_EXP BASIC_TY_EXP1,BASIC_TY_EXP1left,_))::
rest671) => let val result=MlyValue.CART_PROD((
 
      BASIC_TY_EXP1::BASIC_TY_EXP2::nil 
      ))
 in (LrTable.NT 22,(result,BASIC_TY_EXP1left,BASIC_TY_EXP2right),
rest671) end
| (29,(_,(MlyValue.CART_PROD CART_PROD,_,CART_PROD1right))::_::(_,(
MlyValue.BASIC_TY_EXP BASIC_TY_EXP,BASIC_TY_EXP1left,_))::rest671) => 
let val result=MlyValue.CART_PROD(( BASIC_TY_EXP::CART_PROD ))
 in (LrTable.NT 22,(result,BASIC_TY_EXP1left,CART_PROD1right),rest671)
 end
| (30,(_,(MlyValue.BASIC_TY_EXP BASIC_TY_EXP,BASIC_TY_EXP1left,
BASIC_TY_EXP1right))::rest671) => let val result=MlyValue.TY_EXP((
BASIC_TY_EXP))
 in (LrTable.NT 20,(result,BASIC_TY_EXP1left,BASIC_TY_EXP1right),
rest671) end
| (31,(_,(MlyValue.CART_PROD CART_PROD,CART_PROD1left,CART_PROD1right)
)::rest671) => let val result=MlyValue.TY_EXP((
 Ast.ty_con_exp(Ast.TUPLE_TY_CON,CART_PROD) ))
 in (LrTable.NT 20,(result,CART_PROD1left,CART_PROD1right),rest671)
 end
| (32,(_,(MlyValue.TY_EXP TY_EXP2,_,TY_EXP2right))::_::(_,(
MlyValue.TY_EXP TY_EXP1,TY_EXP1left,_))::rest671) => let val result=
MlyValue.TY_EXP((
 
      Ast.ty_con_exp(Ast.THIN_ARROW, TY_EXP1::TY_EXP2::nil) 
      )
)
 in (LrTable.NT 20,(result,TY_EXP1left,TY_EXP2right),rest671) end
| (33,(_,(MlyValue.FUN_DECS FUN_DECS,_,FUN_DECS1right))::(_,(_,
FUN1left,_))::rest671) => let val result=MlyValue.FUN_DEC_LIST((
 FUN_DECS ))
 in (LrTable.NT 15,(result,FUN1left,FUN_DECS1right),rest671) end
| (34,(_,(MlyValue.EXP EXP,_,EXP1right))::_::(_,(MlyValue.PAT PAT,_,_)
)::(_,(MlyValue.ID ID,ID1left,_))::rest671) => let val result=
MlyValue.FUN_DEC((
 {
      func=Ast.string_to_symbol( Ast.func_sym, ID ),
      pat=PAT,
      exp=EXP,
      dec_info=Ast.no_dec_info()
      } 
))
 in (LrTable.NT 17,(result,ID1left,EXP1right),rest671) end
| (35,(_,(MlyValue.EXP EXP,_,EXP1right))::_::(_,(MlyValue.TY_EXP 
TY_EXP2,_,_))::_::_::(_,(MlyValue.TY_EXP TY_EXP1,_,_))::_::(_,(
MlyValue.PAT PAT,_,_))::_::(_,(MlyValue.ID ID,ID1left,_))::rest671)
 => let val result=MlyValue.FUN_DEC((
 {
      func=Ast.string_to_symbol( Ast.func_sym, ID ),
      pat=PAT,
      exp=EXP,
      dec_info= 
        let val TE = 
          Ast.ty_con_exp( Ast.THIN_ARROW, TY_EXP1::TY_EXP2::nil )
        in
          {
            schematic_vars = Ast.vars_in_ty_exp TE,
            ty_exp = TE
            }
        end
      } 
))
 in (LrTable.NT 17,(result,ID1left,EXP1right),rest671) end
| (36,(_,(MlyValue.FUN_DEC FUN_DEC,FUN_DEC1left,FUN_DEC1right))::
rest671) => let val result=MlyValue.FUN_DECS(( FUN_DEC :: nil ))
 in (LrTable.NT 16,(result,FUN_DEC1left,FUN_DEC1right),rest671) end
| (37,(_,(MlyValue.FUN_DECS FUN_DECS,_,FUN_DECS1right))::_::(_,(
MlyValue.FUN_DEC FUN_DEC,FUN_DEC1left,_))::rest671) => let val result=
MlyValue.FUN_DECS(( FUN_DEC :: FUN_DECS ))
 in (LrTable.NT 16,(result,FUN_DEC1left,FUN_DECS1right),rest671) end
| (38,(_,(_,_,RPAR1right))::(_,(MlyValue.PAT PAT,_,_))::(_,(_,
LPAR1left,_))::rest671) => let val result=MlyValue.PAT(( PAT ))
 in (LrTable.NT 13,(result,LPAR1left,RPAR1right),rest671) end
| (39,(_,(_,_,RPAR1right))::(_,(MlyValue.PAT_LIST PAT_LIST,_,_))::_::(
_,(MlyValue.PAT PAT,_,_))::(_,(_,LPAR1left,_))::rest671) => let val 
result=MlyValue.PAT((
 Ast.app_exp {
      func=Ast.TUPLE,
      args=PAT::PAT_LIST,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 13,(result,LPAR1left,RPAR1right),rest671) end
| (40,(_,(MlyValue.PAT PAT2,_,PAT2right))::_::(_,(MlyValue.PAT PAT1,
PAT1left,_))::rest671) => let val result=MlyValue.PAT((
 Ast.app_exp {
      func=Ast.CONS,
      args=PAT1::PAT2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 13,(result,PAT1left,PAT2right),rest671) end
| (41,(_,(_,_,RPAR1right))::(_,(MlyValue.PAT_LIST PAT_LIST,_,_))::_::(
_,(MlyValue.ID ID,ID1left,_))::rest671) => let val result=MlyValue.PAT
((
 Ast.app_exp {
      func=Ast.string_to_symbol( Ast.var_sym, ID ),
      args=PAT_LIST,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 13,(result,ID1left,RPAR1right),rest671) end
| (42,(_,(MlyValue.PAT PAT,_,PAT1right))::_::(_,(MlyValue.ID ID,
ID1left,_))::rest671) => let val result=MlyValue.PAT((
 Ast.as_exp {
      var=Ast.string_to_symbol( Ast.var_sym, ID ),
      pat=PAT, 
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 13,(result,ID1left,PAT1right),rest671) end
| (43,(_,(MlyValue.ID ID2,_,ID2right))::(_,(MlyValue.ID ID1,ID1left,_)
)::rest671) => let val result=MlyValue.PAT((
 Ast.app_exp {
      func=Ast.string_to_symbol( Ast.var_sym, ID1 ),
      args=[ Ast.app_exp{
        func=Ast.string_to_symbol( Ast.var_sym, ID2 ),
        args=nil,
        exp_info=Ast.no_exp_info() } ],
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 13,(result,ID1left,ID2right),rest671) end
| (44,(_,(MlyValue.ID ID,ID1left,ID1right))::rest671) => let val 
result=MlyValue.PAT((
 Ast.app_exp {
      func=Ast.string_to_symbol( Ast.var_sym, ID ),
      args=nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 13,(result,ID1left,ID1right),rest671) end
| (45,(_,(MlyValue.PAT PAT,PAT1left,PAT1right))::rest671) => let val 
result=MlyValue.PAT_LIST(( PAT::nil ))
 in (LrTable.NT 14,(result,PAT1left,PAT1right),rest671) end
| (46,(_,(MlyValue.PAT_LIST PAT_LIST,_,PAT_LIST1right))::_::(_,(
MlyValue.PAT PAT,PAT1left,_))::rest671) => let val result=
MlyValue.PAT_LIST(( PAT::PAT_LIST ))
 in (LrTable.NT 14,(result,PAT1left,PAT_LIST1right),rest671) end
| (47,(_,(MlyValue.ID ID,_,ID1right))::(_,(_,RAISE1left,_))::rest671)
 => let val result=MlyValue.EXP((
 Ast.app_exp {
      func = Ast.string_to_qsymbol ID,
      args = [],
      exp_info = Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,RAISE1left,ID1right),rest671) end
| (48,(_,(_,_,RPAR1right))::(_,(MlyValue.EXP EXP,_,_))::(_,(_,
LPAR1left,_))::rest671) => let val result=MlyValue.EXP(( EXP ))
 in (LrTable.NT 11,(result,LPAR1left,RPAR1right),rest671) end
| (49,(_,(_,_,RPAR1right))::(_,(MlyValue.EXP_LIST EXP_LIST,_,_))::_::(
_,(MlyValue.EXP EXP,_,_))::(_,(_,LPAR1left,_))::rest671) => let val 
result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.TUPLE,
      args=EXP::EXP_LIST,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,LPAR1left,RPAR1right),rest671) end
| (50,(_,(_,_,RPAR1right))::(_,(MlyValue.EXP_LIST EXP_LIST,_,_))::_::(
_,(MlyValue.ID ID,ID1left,_))::rest671) => let val result=MlyValue.EXP
((
 Ast.app_exp {
      func=Ast.string_to_symbol( Ast.func_sym, ID ),
      args=EXP_LIST,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,ID1left,RPAR1right),rest671) end
| (51,(_,(MlyValue.ID ID2,_,ID2right))::(_,(MlyValue.ID ID1,ID1left,_)
)::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func = Ast.string_to_symbol( Ast.func_sym, ID1 ),
      args = Ast.app_exp {
        func = Ast.string_to_symbol' ID2,
        args = nil,
        exp_info = Ast.no_exp_info()
        }
        ::
        nil,
      exp_info = Ast.no_exp_info() 
      } 
))
 in (LrTable.NT 11,(result,ID1left,ID2right),rest671) end
| (52,(_,(MlyValue.INT INT,_,INT1right))::(_,(MlyValue.ID ID,ID1left,_
))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func = Ast.string_to_symbol( Ast.func_sym, ID ),
      args = Ast.app_exp {
        func = Ast.int_to_symbol INT,
        args = nil,
        exp_info = Ast.no_exp_info()
        }
        ::
        nil,
      exp_info = Ast.no_exp_info() 
      } 
))
 in (LrTable.NT 11,(result,ID1left,INT1right),rest671) end
| (53,(_,(MlyValue.REAL REAL,_,REAL1right))::(_,(MlyValue.ID ID,
ID1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func = Ast.string_to_symbol( Ast.func_sym, ID ),
      args = Ast.app_exp {
        func = Ast.real_to_symbol REAL,
        args = nil,
        exp_info = Ast.no_exp_info()
        }
        ::
        nil,
      exp_info = Ast.no_exp_info() 
      } 
))
 in (LrTable.NT 11,(result,ID1left,REAL1right),rest671) end
| (54,(_,(MlyValue.ID ID,ID1left,ID1right))::rest671) => let val 
result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.string_to_symbol' ID,
      args=nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,ID1left,ID1right),rest671) end
| (55,(_,(MlyValue.INT INT,INT1left,INT1right))::rest671) => let val 
result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.int_to_symbol INT,
      args=nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,INT1left,INT1right),rest671) end
| (56,(_,(MlyValue.REAL REAL,REAL1left,REAL1right))::rest671) => let 
val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.real_to_symbol REAL,
      args=nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,REAL1left,REAL1right),rest671) end
| (57,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.SEMICOLON,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (58,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.EQ,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (59,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.LESS',
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (60,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.MUL,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (61,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.DIV,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (62,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.PLUS,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (63,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.MINUS,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (64,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.CONS,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (65,(_,(MlyValue.EXP EXP2,_,EXP2right))::_::(_,(MlyValue.EXP EXP1,
EXP1left,_))::rest671) => let val result=MlyValue.EXP((
 Ast.app_exp {
      func=Ast.APPEND,
      args=EXP1::EXP2::nil,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,EXP1left,EXP2right),rest671) end
| (66,(_,(MlyValue.RULE_LIST RULE_LIST,_,RULE_LIST1right))::_::(_,(
MlyValue.EXP EXP,_,_))::(_,(_,CASE1left,_))::rest671) => let val 
result=MlyValue.EXP((
 Ast.case_exp {
      exp=EXP,
      rules=RULE_LIST,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,CASE1left,RULE_LIST1right),rest671) end
| (67,(_,(_,_,END1right))::(_,(MlyValue.EXP EXP,_,_))::_::(_,(
MlyValue.FUN_DEC_LIST FUN_DEC_LIST,_,_))::(_,(_,LET1left,_))::rest671)
 => let val result=MlyValue.EXP((
 Ast.let_exp {
      dec_list=FUN_DEC_LIST,
      exp=EXP,
      exp_info=Ast.no_exp_info()
      } 
))
 in (LrTable.NT 11,(result,LET1left,END1right),rest671) end
| (68,(_,(MlyValue.EXP EXP,EXP1left,EXP1right))::rest671) => let val 
result=MlyValue.EXP_LIST(( EXP::nil ))
 in (LrTable.NT 12,(result,EXP1left,EXP1right),rest671) end
| (69,(_,(MlyValue.EXP_LIST EXP_LIST,_,EXP_LIST1right))::_::(_,(
MlyValue.EXP EXP,EXP1left,_))::rest671) => let val result=
MlyValue.EXP_LIST(( EXP::EXP_LIST ))
 in (LrTable.NT 12,(result,EXP1left,EXP_LIST1right),rest671) end
| (70,(_,(MlyValue.EXP EXP,_,EXP1right))::_::(_,(MlyValue.PAT PAT,
PAT1left,_))::rest671) => let val result=MlyValue.RULE_LIST((
 Ast.mk_new_rule(PAT,EXP) :: nil ))
 in (LrTable.NT 19,(result,PAT1left,EXP1right),rest671) end
| (71,(_,(MlyValue.RULE_LIST RULE_LIST,_,RULE_LIST1right))::_::(_,(
MlyValue.EXP EXP,_,_))::_::(_,(MlyValue.PAT PAT,PAT1left,_))::rest671)
 => let val result=MlyValue.RULE_LIST((
 
      Ast.mk_new_rule(PAT,EXP) :: RULE_LIST 
      ))
 in (LrTable.NT 19,(result,PAT1left,RULE_LIST1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : ML_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun FUN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun VAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun DATATYPE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun TYPE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun LET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun IN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun CASE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun OF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun AS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun VBAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun THIN_ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun EQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun LESS' (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun MUL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun DIV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun PRIME (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun CONS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun APPEND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun RAISE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun EXCEPTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun INT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.INT i,p1,p2))
fun REAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.REAL i,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.ID i,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
end
end
