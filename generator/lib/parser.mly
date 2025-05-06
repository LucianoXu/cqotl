%{
  open Ast
%}

%token <string> ID
%token <int> INT

(* character symbols *)
%token COLON COMMA PERIOD RNDARROW ASSIGN STARASSIGN KET0 SEMICOLON LBRACK RBRACK EQ TILDE LBRACE RBRACE LANGLE RANGLE PLUS LPAREN RPAREN STAR UNDERSCORE

(* token for commands *)
%token DEF VAR CHECK SHOW SHOWALL UNDO PAUSE PROVE QED

(* token for tactics *)
%token SORRY
%token R_SKIP

%token TYPE PROP QVLIST OPTPAIR CTYPE CVAR QREG PROG BIT CTERM STYPE OTYPE DTYPE

(* token for propositions *)
%token PROP_UNITARY PROP_ASSN PROP_MEAS

(* token for terms *)
%token SKIP INIT UNITARY_PROG MEAS IF THEN ELSE WHILE DO END
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
  | DEF x = ID COLON t = terms ASSIGN e = terms PERIOD { Def {x; t; e} }
  | DEF x = ID ASSIGN e = terms PERIOD { DefWithoutType {x; e} }
  | VAR x = ID COLON t = terms PERIOD  { Var {x; t} }
  | CHECK e = terms PERIOD { Check e }
  | SHOW x = ID PERIOD { Show x }
  | SHOWALL PERIOD { ShowAll }
  | UNDO PERIOD { Undo }
  | PAUSE PERIOD { Pause }
  | PROVE x = ID COLON p = terms PERIOD { Prove {x; p} }
  | QED PERIOD { QED }
  | t = tactic { Tactic t }

tactic:
  | SORRY PERIOD { Sorry }
  | R_SKIP PERIOD { R_SKIP }

terms:
  | v = ID { Var v }

  | LPAREN t1 = terms RPAREN { t1 }

  | TYPE { Type }
  | PROP { Prop }
  | QVLIST { QVList }
  | OPTPAIR { OptPair }
  | CTYPE { CType }
  | CVAR LBRACK t = terms RBRACK { CVar t }
  | QREG LBRACK t = terms RBRACK { QReg t }
  | PROG { Prog }
  | BIT { Bit }

  | CTERM LBRACK t = terms RBRACK { CTerm t }
  | STYPE { SType }
  | OTYPE LBRACK t1 = terms COMMA t2 = terms RBRACK { OType (t1, t2) }
  | DTYPE LBRACK t1 = terms COMMA t2 = terms RBRACK { DType (t1, t2) }
  | t1 = terms STAR t2 = terms { Star (t1, t2) }
  | LPAREN t1 = terms COMMA t2 = terms RPAREN { Pair (t1, t2) }
  | LBRACK idls = id_list RBRACK { QVListTerm idls }
  | t1 = terms UNDERSCORE t2 = terms COMMA t3 = terms { Subscript (t1, t2, t3) }

  | op = opt { OptTerm op }
  | s = stmt_seq { ProgTerm s }
  | p = props { PropTerm p }


id_list:
  | t = ID COMMA tls = id_list { t :: tls }
  | t = ID { [t] }

opt:
  | o1 = terms PLUS o2 = terms { Add {o1; o2} }

stmt_seq:
  | s = stmt ss = stmt_seq { s :: ss }
  | s = stmt { SingleCmd s }

stmt:
  | SKIP                                                                     { Skip }
  | id = ID ASSIGN t = terms                                          { Assign {x=id; t=t} }
  | id = ID RNDARROW t = terms                                     { PAssign {x=id; t=t} }
  | INIT q           = terms                                              { InitQubit q }
  | UNITARY_PROG u_opt = terms qs = terms                            { Unitary {u_opt; qs} }
  | id = ID ASSIGN MEAS m_opt = terms                    { Meas {x=id; m_opt=m_opt} }
  | IF b = terms THEN s1 = terms ELSE s2 = terms END          { IfMeas {b; s1; s2} }
  | WHILE b    = terms DO s = terms END                          { WhileMeas {b; s} }


props:
  | PROP_UNITARY t = terms { Unitary t }
  | PROP_ASSN t = terms { Assn t }
  | PROP_MEAS t = terms { Meas t }
  | LBRACE pre = terms RBRACE s1 = terms TILDE s2 = terms LBRACE post = terms RBRACE { Judgement {pre; s1; s2; post} }
  | t1 = terms EQ t2 = terms { Eq {t1; t2} }
