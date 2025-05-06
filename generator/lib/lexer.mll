{
    open Parser
    exception Error of string
}

let whitespace  = [' ' '\t' '\r' '\n']
let digit       = ['0'-'9']
let alpha       = ['a'-'z' 'A'-'Z']
(* let id          = alpha (alpha | digit | '_')* *)
let id          = alpha (alpha | digit)*

rule token = parse
    | whitespace                    { token lexbuf }
    | "(*"                          { comment lexbuf; token lexbuf }

    (* Symbols *)
    | ":"                           { COLON }
    | ","                           { COMMA }
    | "."                           { PERIOD }
    | "<-$"                         { RNDARROW }
    | ":="                          { ASSIGN }
    | "*="                          { STARASSIGN }
    | "|0>"                         { KET0 }
    | ";"                           { SEMICOLON }
    | "["                           { LBRACK }
    | "]"                           { RBRACK }
    | "="                           { EQ }
    | "~"                           { TILDE }
    | "{"                           { LBRACE }
    | "}"                           { RBRACE }
    | "<"                           { LANGLE }
    | ">"                           { RANGLE }
    | "+"                           { PLUS }
    | "("                           { LPAREN }
    | ")"                           { RPAREN }
    | "*"                           { STAR }
    | "_"                           { UNDERSCORE }

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
    | "r_skip"                      { R_SKIP }

    (* Types *)
    | "Type"                        { TYPE }
    | "Prop"                        { PROP }
    | "QVList"                      { QVLIST }
    | "OptPair"                     { OPTPAIR }
    | "CType"                       { CTYPE }
    | "CVar"                        { CVAR }
    | "QReg"                        { QREG }
    | "Prog"                        { PROG }
    | "Bit"                         { BIT }

    | "CTerm"                       { CTERM }
    | "SType"                       { STYPE }
    | "OType"                       { OTYPE }
    | "DType"                       { DTYPE }


    (* Propositions *)
    | "Unitary"                     { PROP_UNITARY }
    | "Assn"                        { PROP_ASSN }
    | "Meas"                        { PROP_MEAS }
    (* Judgement *)
    (* eq = *)


    (* Terms *)
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

    | id as v                       { ID v }
    (* Does it mean that only one-digit number is parsed? *)
    | digit as d                    { INT (int_of_char d - 48) }
    | eof                           { EOF }

    | _                             { raise (Error ("Unexpected char: " ^ Lexing.lexeme lexbuf))}

and comment = parse
    | "*)"                     { () }  (* End of comment *)
    | eof                      { raise (Error "Unterminated comment") }
    | _                        { comment lexbuf }  (* Skip any other character *)
