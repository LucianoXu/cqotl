let parse_top (input : string) : Ast.command list =
  let lexbuf = Lexing.from_string input in
  try Parser.top Lexer.token lexbuf
  with
  | Parser.Error -> failwith "Syntax error"
  | Lexer.Error msg -> failwith ("Lexer error: " ^ msg)