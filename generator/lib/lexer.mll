{
    open Parser
    exception Error of string
}

let whitespace  = [' ' '\t' '\r' '\n']
let digit       = ['0'-'9']
let alpha       = ['a'-'z' 'A'-'Z']
let var         = alpha (alpha | digit | '_')*

rule token = parse
    | whitespace                    { token lexbuf }
    | "skip"                        { SKIP }
    | ":="                          { ASSIGN }
    | "|0>"                         { KET0 }
    | ";"                           { SEMICOLON }
    | "["                           { LBRACK }
    | "]"                           { RBRACK }
    | "if"                          { IF }
    | "while"                       { WHILE }
    | "then"                        { THEN }
    | "do"                          { DO }
    | "od"                          { OD }
    | "="                           { EQ }
    | "H" | "X" | "Z" | "M" as op   { UNITARY_OP  (String.make 1 op) }
    | var   as v                    { Var v }
    | digit as d                    { INT (int_of_char d - 48) }
    | eof                           { EOF }
    | _                             { raise (Error ("Unexpected char: " ^ Lexing.lexeme lexbuf))}