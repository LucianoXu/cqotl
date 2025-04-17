let parse_program (input : string) : Ast.stmt_seq =
  let lexbuf = Lexing.from_string input in
  try Parser.program Lexer.token lexbuf
  with
  | Parser.Error -> failwith "Syntax error"
  | Lexer.Error msg -> failwith ("Lexer error: " ^ msg)