%{
  open Ast
%}

%token <string> ID
%token <int> INT

%token COLON COMMA PERIOD ASSIGN KET0 SEMICOLON LBRACK RBRACK EQ TILDE LBRACE RBRACE PLUS

(* token for commands *)
%token DEF VAR CHECK SHOW SHOWALL UNDO

(* token for types *)
%token QVAR QREG OPT LOPT ASSERTION PROGRAM

(* token for terms *)
%token SKIP IF THEN ELSE WHILE DO END
%token EOF

%start top
%type <Ast.command list> top

%%

top:
  | cl = command_list EOF { cl }

command_list:
  | c = command cl = command_list { c :: cl }
  | c = command { [c] }

command:
  | DEF x = ID COLON t = types ASSIGN e = terms PERIOD { Def {x; t; e} }
  | VAR x = ID COLON t = types PERIOD  { Var {x; t} }
  | CHECK e = terms PERIOD { Check e }
  | SHOW x = ID PERIOD { Show x }
  | SHOWALL PERIOD { ShowAll }
  | UNDO PERIOD { Undo }

types:
  | QVAR { QVar }
  | QREG d = INT { QReg d }
  | OPT d = INT { Opt d }
  | LOPT { LOpt }
  | ASSERTION { Assertion }
  | PROGRAM { Program }
  | LBRACE pre = terms RBRACE s1 = terms TILDE s2 = terms LBRACE post = terms RBRACE { Judgement {pre; s1; s2; post} }

terms:
  | v = ID { Var v }
  | qs = qreg { QRegTerm qs }
  | op = opt { OptTerm op }
  | lop = lopt { LOptTerm lop }
  (* we don't parse assertion, but to construct them by proofs *)
  | s = stmt_seq { Stmt s }
  (* we don't parse proofs *)


(* for qubit list *)
qreg:
  | LBRACK ids = id_list RBRACK { ids }

id_list:
  | id = ID COMMA ids = id_list { id :: ids }
  | id = ID { [id] }

opt:
  | o1 = terms PLUS o2 = terms { Add {o1; o2} }

lopt:
  | opt = terms qs = qreg { Pair {opt; qs}}

stmt_seq:
  | s = stmt ss = stmt_seq { s :: ss }
  | s = stmt { SingleCmd s }

stmt:
  | SKIP                                                                     { Skip }
  | q           = ID ASSIGN KET0                                             { InitQubit q }
  | u_opt = terms qs = qreg { Unitary {u_opt; qs} }
  | IF m_opt = terms THEN s1 = terms ELSE s2 = terms END          { IfMeas {m_opt; s1; s2} }
  | WHILE m_opt    = terms DO s = terms END              { WhileMeas {m_opt; s} }

