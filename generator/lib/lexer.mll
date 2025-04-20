{
    open Parser
    exception Error of string
}

let whitespace  = [' ' '\t' '\r' '\n']
let digit       = ['0'-'9']
let alpha       = ['a'-'z' 'A'-'Z']
let id          = alpha (alpha | digit | '_')*

rule token = parse
    | whitespace                    { token lexbuf }
    | "(*"                          { comment lexbuf; token lexbuf }

    (* Symbols *)
    | ":"                           { COLON }
    | ","                           { COMMA }
    | "."                           { PERIOD }
    | ":="                          { ASSIGN }
    | "|0>"                         { KET0 }
    | ";"                           { SEMICOLON }
    | "["                           { LBRACK }
    | "]"                           { RBRACK }
    | "="                           { EQ }
    | "~"                           { TILDE }
    | "{"                           { LBRACE }
    | "}"                           { RBRACE }
    | "+"                           { PLUS }

    (* Commands *)
    | "Def"                         { DEF }
    | "Var"                         { VAR }
    | "Check"                       { CHECK }
    | "Show"                        { SHOW }
    | "ShowAll"                     { SHOWALL }
    | "Undo"                        { UNDO }

    (* Types *)
    | "QVar"                        { QVAR }
    | "QReg"                        { QREG }
    | "Opt"                         { OPT }
    | "LOpt"                        { LOPT }
    | "Assertion"                   { ASSERTION }
    | "Program"                     { PROGRAM }

    (* Terms *)
    | "skip"                        { SKIP }
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
