open Ast

let parse_top (input : string) : Ast.command list =
  let lexbuf = Lexing.from_string input in
  try Parser.top Lexer.token lexbuf
  with
  | Parser.Error -> raise (SyntaxError "Syntax error")
  | Lexer.Error msg -> raise (SyntaxError ("Lexer error: " ^ msg))