(*
require "basis.__string";
require "basis.__int";
require "basis.__bool";
require "pp.sml";
require "base-sig.sml";
require "parser2.sml";
require "join.sml";
require "ML-grm-sig.sml";
require "ML-grm.sml";
require "ML-lex.sml";
require "lib.sml";
require "ast.sml";
*)

(* File: parse.sml 
   Created 1993-05-24.
   Modified 1996-06-04.
  Renamed from io.sml to parse.sml 1999-12-09 when structure Print was 
  removed from this file and reimplemented in print.sml
*)

structure MLLrVals : ML_LRVALS =
   MLLrValsFun(structure Token = LrParser.Token );

structure MLLex : LEXER =
   MLLexFun(structure Tokens = MLLrVals.Tokens );

structure MLParser : PARSER =
   Join(structure ParserData = MLLrVals.ParserData
        structure Lex = MLLex
	structure LrParser = LrParser);

signature PARSE =
sig
val parse_declarations : string -> Ast.parse_result list
val parse_dec : string -> Ast.dec 
val parse_decs : string -> Ast.dec list
val parse_type_dec : string -> Ast.type_dec 
val parse_datatype_dec : string -> Ast.datatype_dec 
val parse_datatype_decs : string -> Ast.datatype_dec list
val parse_exp : string -> Ast.exp
val parse_ty_exp : string -> Ast.ty_exp
end

structure Parse : PARSE =
struct
open Lib

fun string_reader S =
  let val next = ref S in
    fn _ => !next before next := ""
  end

fun parse_declarations (S:string) : Ast.parse_result list = 
  let fun print_error( Msg, Line1,Line2) = (
    output( !std_err,
    "Syntax error at line " ^ Int.toString(Line1) ^
     ": " ^ Msg ^ "\n");
    flush_out( !std_err ) )
  in
case
  MLParser.parse(
    0,
    MLParser.makeLexer (string_reader S),
    print_error,
    ()
    )
of (X,Y) =>X 
  end

fun parse_decs S =
  case parse_declarations S of Ast.parsed_fun( Ds ) :: nil => Ds

fun parse_dec S = case parse_decs S of D::nil => D

fun parse_type_dec S =
  case parse_declarations S of Ast.parsed_type TD :: nil => TD

fun parse_datatype_decs S =
  case parse_declarations S of 
    Ast.parsed_datatype( DDs ) :: nil => DDs

fun parse_datatype_dec S =
  case parse_datatype_decs S of DD::nil => DD

fun parse_exp S =
  case parse_dec("fun f(X) = " ^ S) of {exp,...} => exp

fun parse_ty_exp S =
  case parse_declarations( "type t = " ^ S ) of
    (Ast.parsed_type { ty_exp, ty_pars=nil, ... }) :: nil => ty_exp

end (* Parse *)


