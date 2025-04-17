%{
  open Ast
%}

%token <string> Var UNITARY_OP
%token <int> INT
%token SKIP ASSIGN KET0 SEMICOLON IF WHILE THEN DO END EQ EOF
%token LBRACK RBRACK

%start program
%type <Ast.stmt_seq> program

%%

program:
  | s = stmt_seq EOF { s }

stmt_seq:
  | s = stmt ss = stmt_seq { s :: ss }
  | s = stmt { SingleCmd s }

stmt:
  | SKIP SEMICOLON                                                                     { Skip }
  | q           = Var ASSIGN KET0 SEMICOLON                                            { InitQubit q }
  | op          = UNITARY_OP LBRACK q = Var RBRACK SEMICOLON                           { ApplyUnitary (op, [q]) }
  | IF op       = UNITARY_OP LBRACK q = Var RBRACK EQ n=INT THEN s = stmt_seq END          { IfMeas (op, q, [(n, s)]) }
  | WHILE op    = UNITARY_OP LBRACK q = Var RBRACK EQ INT DO s = stmt_seq END              { WhileMeas (op, q, s) }

