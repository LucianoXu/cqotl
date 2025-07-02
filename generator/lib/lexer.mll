{
    open Lexing
    open Parser
    exception Error of string

    let newline lexbuf =
        let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- {
            pos with
            pos_lnum = pos.pos_lnum + 1;
            pos_bol = pos.pos_cnum;
        }
}

let whitespace  = [' ' '\t']
let digit       = ['0'-'9']
let number      = '0' | ['1'-'9' '-'] (digit*)
let alpha       = ['a'-'z' 'A'-'Z' ''']
let id          = alpha (alpha | digit)*

rule token = parse
    | '\n'                          { newline lexbuf; token lexbuf }
    | whitespace                    { token lexbuf }
    | number as n                    { NUM (int_of_string n) }

    | "(*"                          { comment lexbuf; token lexbuf }

    (* Symbols *)
    | "\\/"                         { VEE }
    | "/\\"                         { WEDGE }
    | "-->"                         { LONGARROW }
    | "->"                          { ARROW }
    | "=>"                          { DARROW }
    | ":"                           { COLON }
    | ","                           { COMMA }
    | "."                           { PERIOD }
    | "|->"                         { MAPSTO }
    | "|-"                          { VDASH }
    | "<-$"                         { RNDARROW }
    | "<-"                          { LARROW }
    | ":="                          { ASSIGN }
    | ";"                           { SEMICOLON }
    | "["                           { LBRACK }
    | "]"                           { RBRACK }
    | "<="                          { LEQ }
    | "=="                          { EQEQ }
    | "="                           { EQ }
    | "~"                           { TILDE }
    | "{"                           { LBRACE }
    | "}"                           { RBRACE }
    | "+"                           { PLUS }
    | "("                           { LPAREN }
    | ")"                           { RPAREN }
    | "*"                           { STAR }
    | "@@"                          { ATAT }
    | "@"                           { AT }
    | "#"                           { HASH }
    | "|"                           { VBAR }
    | ">"                           { RANGLE }
    | "<"                           { LANGLE }
    | "^D"                          { ADJ }
    | '_'                           { UNDERSCORE }

    (* Commands *)
    | "Def"                         { DEF }
    | "Var"                         { VAR }
    | "Check"                       { CHECK }
    | "Show"                        { SHOW }
    | "ShowAll"                     { SHOWALL }
    | "Undo"                        { UNDO }
    | "Pause"                       { PAUSE }
    | "Prove"                       { PROVE }
    | "QED"                         { QED }
    
    (* Tactics *)
    | "sorry"                       { SORRY }
    | "expand"                      { EXPAND }
    | "refl"                        { REFL }
    | "destruct"                    { DESTRUCT }
    | "case"                        { CASE }
    | "intro"                       { INTRO }
    | "revert"                      { REVERT }
    | "apply"                       { APPLY }
    | "choose"                      { CHOOSE }
    | "split"                       { SPLIT }
    | "by_lean"                     { BYLEAN }
    | "by_rocq"                     { BYROCQ }
    | "simpl"                       { SIMPL }
    | "rewrite"                     { REWRITE }
    | "rwrule"                      { RWRULE }

    | "r_pre"                       { R_PRE }
    | "r_post"                      { R_POST }
    | "r_skip"                      { R_SKIP }
    | "r_seq"                       { R_SEQ }
    | "r_assign"                    { R_ASSIGN }
    | "r_initq"                     { R_INITQ }
    | "r_unitary"                   { R_UNITARY }
    | "r_meas"                      { R_MEAS }
    | "r_if"                        { R_IF }
    | "r_while"                     { R_WHILE }
    | "r_while_while"               { R_WHILE_WHILE }
    | "r_meas_meas"                 { R_MEAS_MEAS }
    | "r_meas_sample"               { R_MEAS_SAMPLE }
    | "id"                          { SWITCH_ID }
    | "swap"                        { SWITCH_SWAP }
    
    | "judge_swap"                  { JUDGE_SWAP }
    | "cq_entail"                   { CQ_ENTAIL }
    | "dirac"                       { DIRAC }
    | "simpl_entail"                { SIMPL_ENTAIL }
    | "entail_trans"                { ENTAIL_TRANS }
    | "cylinder_ext"                { CYLINDER_EXT }


    (* terms *)
    | "forall"                      { FORALL }
    | "fun"                         { FUN }
    | "tr"                          { TR }

    | "skip"                        { SKIP }
    | "init"                        { INIT }
    | "unitary"                     { UNITARY_PROG }
    | "meas"                        { MEAS }
    | "if"                          { IF }
    | "then"                        { THEN }
    | "else"                        { ELSE }
    | "while"                       { WHILE }
    | "do"                          { DO }
    | "end"                         { END }

    | "0O"                          { ZEROO }
    | "1O"                          { ONEO }

    | id as v                       { ID v }
    | eof                           { EOF }

    | _                             { UNEXPECTED }

and comment = parse
    | "*)"                     { () }  (* End of comment *)
    | eof                      { () }
    | '\n'                     { newline lexbuf; comment lexbuf }
    | _                        { comment lexbuf }  (* Skip any other character *)
