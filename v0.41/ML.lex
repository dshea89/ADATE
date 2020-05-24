
(* File: ML.lex
   Modified 1993-05-24
*)

structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val line = ref 1
exception ml_lex_gen;
val error = fn X => (
  Lib.output( !Lib.std_err,X^"\n");
  Lib.flush_out( !Lib.std_err );
  raise ml_lex_gen)
val eof = fn () => Tokens.EOF(!line,!line)
%%
%header (functor MLLexFun( structure Tokens : ML_TOKENS ) : LEXER );
%%
<INITIAL>\n => (Lib.inc line; lex());
<INITIAL>[\ \t]+ => (lex());
<INITIAL>"(" => (Tokens.LPAR(!line,!line));
<INITIAL>")" => (Tokens.RPAR(!line,!line));
<INITIAL>"|" => (Tokens.VBAR(!line,!line));
<INITIAL>"=>" => (Tokens.ARROW(!line,!line));
<INITIAL>"->" => (Tokens.THIN_ARROW(!line,!line));
<INITIAL>"," => (Tokens.COMMA(!line,!line));
<INITIAL>";" => (Tokens.SEMICOLON(!line,!line));
<INITIAL>"=" => (Tokens.EQ(!line,!line));
<INITIAL>"<" => (Tokens.LESS'(!line,!line));
<INITIAL>"+" => (Tokens.PLUS(!line,!line));
<INITIAL>"-" => (Tokens.MINUS(!line,!line));
<INITIAL>"/" => (Tokens.DIV(!line,!line));
<INITIAL>"*" => (Tokens.MUL(!line,!line));
<INITIAL>"::" => (Tokens.CONS(!line,!line));
<INITIAL>"@" => (Tokens.APPEND(!line,!line));
<INITIAL>":" => (Tokens.COLON(!line,!line));
<INITIAL>"'" => (Tokens.PRIME(!line,!line));
<INITIAL>~?[0-9]+"."[0-9]+[Ee]~?[0-9]+ => ( Tokens.REAL( valOf(Real.fromString yytext), !line, !line ) );
<INITIAL>~?[0-9]+"."[0-9]+ => ( Tokens.REAL( valOf(Real.fromString yytext), !line, !line ) );
<INITIAL>~?[0-9]+ => ( Tokens.INT( valOf(Int.fromString yytext), !line, !line ) );
<INITIAL>[A-Za-z?][A-Za-z0-9_']* => (
  if yytext="fun" then Tokens.FUN(!line,!line)
  else if yytext="val" then Tokens.VAL(!line,!line)
  else if yytext="datatype" then Tokens.DATATYPE(!line,!line)
  else if yytext="type" then Tokens.TYPE(!line,!line)
  else if yytext="let" then Tokens.LET(!line,!line)
  else if yytext="in" then Tokens.IN(!line,!line)
  else if yytext="end" then Tokens.END(!line,!line)
  else if yytext="case" then Tokens.CASE(!line,!line)
  else if yytext="of" then Tokens.OF(!line,!line)
  else if yytext="as" then Tokens.AS(!line,!line)
  else if yytext="and" then Tokens.AND(!line,!line)
  else if yytext="raise" then Tokens.RAISE(!line,!line)
  else if yytext="exception" then Tokens.EXCEPTION(!line,!line)
  else Tokens.ID(yytext,!line,!line)
  );
<INITIAL>. => (error("ML.lex: Bad character "^yytext));




