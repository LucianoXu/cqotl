open Ast

module IE = MenhirLib.IncrementalEngine
module I  = Parser.MenhirInterpreter

exception SyntaxError of string


(* Incremental Parser with loop and entry point *)
(* Incremental Parser loop *)
let rec loop lexbuf (checkpoint : command list I.checkpoint) : command list = 
  match checkpoint with
  | I.InputNeeded _env   ->
    (*The parser needs a token. Request one from the lexer,
      and offer it to the parser, which will produce a new
      checkpoint. Then, repeat *)
      let   token     = Lexer.token lexbuf  in (* Taking the next token from the lexer *)
      let   startp    = lexbuf.lex_start_p     (* Start point at the lex buffer *)
      and   endp      = lexbuf.lex_curr_p   in (* End point at the lex buffer *)
      let checkpoint  = I.offer checkpoint (token, startp, endp) in (* Get the next checkpoint *)
      loop lexbuf checkpoint (* Repeat the loop *)
  | I.Shifting _
  | I.AboutToReduce _     ->
      let checkpoint  = I.resume checkpoint in
      loop lexbuf checkpoint
  | I.HandlingError env ->
      let start_pos       = Lexing.lexeme_start_p lexbuf in
      let offending_token = Lexing.lexeme lexbuf in
      let col             = start_pos.pos_cnum - start_pos.pos_bol in
      let msg = Printf.sprintf
        "Syntax error at column %d near \"%s\""
        col offending_token
      in
      raise (SyntaxError msg)
  | I.Accepted v          ->
      (* The parser has succeeded and produced a semantic value. Print it. *)
      v
  | I.Rejected            ->
      (* The parser rejects this input. This cannot happen, here, because
        we stop as soon as the parser reports [HandlingError]. *)
        assert false

(*  Entry point for parsing the entire string using the incremental API *)
let parse_top_inc (input : string) : command list =
  let lexbuf = Lexing.from_string input in
  try
    let checkpoint  = (Parser.Incremental.main lexbuf.lex_curr_p) in
    (* Drive the incremental parser loop until completion *)
    loop lexbuf checkpoint
  with
  | Lexer.Error msg ->
      let pos = Lexing.lexeme_start_p lexbuf in
      let full_msg = Printf.sprintf "Lexer error at line %d, column %d: %s"
                                    pos.pos_lnum (pos.pos_cnum - pos.pos_bol) msg in
      raise (SyntaxError full_msg)