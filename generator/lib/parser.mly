%{
  open Ast
%}

%token <string> Var UNITARY_OP
%token <int> INT
%token SKIP ASSIGN KET0 SEMICOLON IF WHILE THEN DO OD EQ EOF
%token LBRACK RBRACK

%start program
%type <Ast.stmt> program

%%

program:
  | s = stmt EOF { s }

stmt:
  | SKIP                                                                      { Skip }
  | q           = Var ASSIGN KET0                                             { InitQubit q }
  | op          = UNITARY_OP LBRACK q = Var RBRACK                            { ApplyUnitary (op, [q]) }
  | s1          = stmt SEMICOLON s2   = stmt                                  { Seq (s1, s2) }
  | IF op       = UNITARY_OP LBRACK q = Var RBRACK EQ n=INT THEN s = stmt     { IfMeas (op, q, [(n, s)]) }
  | WHILE op    = UNITARY_OP LBRACK q = Var RBRACK EQ INT DO s = stmt OD      { WhileMeas (op, q, s) }

