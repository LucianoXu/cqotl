open Ast
module I  = Parser.MenhirInterpreter

exception SyntaxError of string

(* keep best commands *)
type best = {
  cp   : command list I.checkpoint;   (* the checkpoint itself *)
  ast  : command list;                (* materialised AST      *)
  size : int;                         (* length of [ast]       *)
}

let empty_best init_cp = { cp = init_cp; ast = []; size = 0; }

let rec drain cp =
  match cp with
  | I.Shifting _ | I.AboutToReduce _ ->
      drain (I.resume cp)
  | _ -> cp                   (* now it is InputNeeded, Accepted or Error *)

let try_accept (cp : _ I.checkpoint) (pos : Lexing.position)
  : command list option =
  let cp' = drain (I.offer cp (Parser.EOF, pos, pos)) in
  match cp' with
  | I.Accepted ast -> Some ast
  | _              -> None           (* parser not complete here *)

type inc_parse_result = 
| Complete of command list
| Partial of command list * string

(* Incremental Parser with loop and entry point *)
(* Incremental Parser loop *)
let rec loop lexbuf (checkpoint : command list I.checkpoint) (bst: best): inc_parse_result = 
  match checkpoint with
  | I.InputNeeded _env   ->
    (*The parser needs a token. Request one from the lexer,
      and offer it to the parser, which will produce a new
      checkpoint. Then, repeat *)
      let   token     = Lexer.token lexbuf  in (* Taking the next token from the lexer *)
      let   startp    = lexbuf.lex_start_p  in (* Start point at the lex buffer *)
      let   endp      = lexbuf.lex_curr_p   in (* End point at the lex buffer *)
      let   bst =
        match try_accept checkpoint endp with
        | Some ast when List.length ast > bst.size ->
              { cp = checkpoint; ast; size = List.length ast }
        | _ -> bst
      in
      let checkpoint  = I.offer checkpoint (token, startp, endp) in (* Get the next checkpoint *)
      loop lexbuf checkpoint bst (* Repeat the loop *)
  | I.Shifting _
  | I.AboutToReduce _     ->
      let checkpoint  = I.resume checkpoint in
        loop lexbuf checkpoint bst
  | I.HandlingError _ ->
      let pos = lexbuf.Lexing.lex_curr_p in
      let offending_token = Lexing.lexeme lexbuf in
      let msg = Printf.sprintf
        "unexpected \"%s\" (line %d, column %d)"
        offending_token pos.pos_lnum (pos.pos_cnum - pos.pos_bol) in
      Partial (bst.ast, msg)
  | I.Accepted v          ->
      (* The parser has succeeded and produced a semantic value. Print it. *)
      Complete v
  | I.Rejected            ->
      (* The parser rejects this input. This cannot happen, here, because
        we stop as soon as the parser reports [HandlingError]. *)
        assert false

(*  Entry point for parsing the entire string using the incremental API *)
let parse_top_inc (input : string) : inc_parse_result =
  let lexbuf = Lexing.from_string input in
  let checkpoint  = (Parser.Incremental.command_list lexbuf.lex_curr_p) in
  let best0 = empty_best checkpoint in
  (* Drive the incremental parser loop until completion *)
  loop lexbuf checkpoint best0


let parse_terms (input : string) : terms =
  let lexbuf = Lexing.from_string input in
  try Parser.terms_eof Lexer.token lexbuf with
  | Parser.Error -> failwith ("Syntax error in terms: " ^ input)
  | Lexer.Error msg -> failwith ("Lexer error: " ^ msg ^ " in terms: " ^ input)

let parse_rw_rule (input : string) : rewriting_rule
  =
  let lexbuf = Lexing.from_string input in
  try Parser.rewriting_rule_eof Lexer.token lexbuf with
  | Parser.Error -> failwith ("Syntax error in rewriting rule: " ^ input)
  | Lexer.Error msg -> failwith ("Lexer error: " ^ msg ^ " in rewriting rule: " ^ input)