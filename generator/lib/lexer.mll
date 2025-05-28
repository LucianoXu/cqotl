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
(* let id          = alpha (alpha | digit | '_')* *)
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
    | "@1"                          { AT1 }
    | "@2"                          { AT2 }
    | ":"                           { COLON }
    | ","                           { COMMA }
    | "."                           { PERIOD }
    | "|->"                         { MAPSTO }
    | "|-"                          { VDASH }
    | "+cq"                         { PLUSCQ }
    | "<-$"                         { RNDARROW }
    | ":="                          { ASSIGN }
    | "*="                          { STARASSIGN }
    | "|0>"                         { KET0 }
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
    | "@"                           { AT }
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
    | "intro"                       { INTRO }
    | "choose"                      { CHOOSE }
    | "split"                       { SPLIT }
    | "by_lean"                     { BYLEAN }
    | "simpl"                       { SIMPL }
    | "r_skip"                      { R_SKIP }
    | "r_seq"                       { R_SEQ }
    | "r_initq"                     { R_INITQ }
    
    | "cq_entail"                   { CQ_ENTAIL }
    | "delabel"                     { DELABEL }
    (* | "seq_front"                   { SEQ_FRONT }
    | "seq_back"                    { SEQ_BACK }
    | "r_unitary1"                  { R_UNITARY1 } *)


    (* terms *)
    | "Type"                        { TYPE }
    | "forall"                      { FORALL }
    | "fun"                         { FUN }

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
    (*

    (* Types *)
    | "Prop"                        { PROP }
    | "QVList"                      { QVLIST }
    | "OptPair"                     { OPTPAIR }
    | "CType"                       { CTYPE }
    | "CVar"                        { CVAR }
    | "QReg"                        { QREG }
    | "Prog"                        { PROG }
    | "CAssn"                       { CASSN }
    | "QAssn"                       { QASSN }
    | "CQAssn"                      { CQASSN }

    | "Bit"                         { BIT }

    | "CTerm"                       { CTERM }
    | "SType"                       { STYPE }
    | "OType"                       { OTYPE }
    | "DType"                       { DTYPE }


    (* Assertions *)
    | "true"                        { TRUE }
    | "false"                       { FALSE }


    (* Propositions *)
    | "Unitary"                     { PROP_UNITARY }
    | "Pos"                         { PROP_POS }
    | "Proj"                        { PROP_PROJ }
    | "Meas"                        { PROP_MEAS }
    (* Judgement *)
    (* eq = *)

    *)

    | id as v                       { ID v }
    | eof                           { EOF }

    | _                             { raise (Error ("Unexpected char: " ^ Lexing.lexeme lexbuf))}

and comment = parse
    | "*)"                     { () }  (* End of comment *)
    | eof                      { raise (Error "Unterminated comment") }
    | '\n'                     { newline lexbuf; comment lexbuf }
    | _                        { comment lexbuf }  (* Skip any other character *)
