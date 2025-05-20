%{
  open Ast
%}

%token <string> ID
%token <int> NUM

(* character symbols *)
%token AT1 AT2 COLON COMMA PERIOD MAPSTO PLUSCQ RNDARROW ASSIGN STARASSIGN KET0 SEMICOLON LBRACK RBRACK LEQ EQEQ EQ TILDE LBRACE RBRACE LANGLE RANGLE PLUS LPAREN RPAREN STAR AT UNDERSCORE

(* token for commands *)
%token DEF VAR CHECK SHOW SHOWALL UNDO PAUSE PROVE QED

(* token for tactics *)
%token SORRY CHOOSE
%token R_SKIP SEQ_FRONT SEQ_BACK R_UNITARY1

%token TYPE PROP QVLIST OPTPAIR CTYPE CVAR QREG PROG CASSN QASSN CQASSN BIT CTERM STYPE OTYPE DTYPE

(* assertions and operators *)
%token TRUE FALSE

(* token for propositions *)
%token PROP_UNITARY PROP_POS PROP_PROJ PROP_MEAS

(* token for Dirac notation *)
%token ONEO ZEROO

(* token for programs *)
%token SKIP INIT UNITARY_PROG MEAS IF THEN ELSE WHILE DO END
%token EOF


/* -- precedence table -- */
%left PLUS
%nonassoc MAPSTO
%left STAR
%nonassoc EQEQ EQ LEQ
%right AT
/**************************/

%start main
%type <Ast.command list> main

%%

main:
  | EOF { [] }
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
  | CHOOSE n = NUM PERIOD { Choose n }
  | R_SKIP PERIOD { R_SKIP }
  | SEQ_FRONT t = terms PERIOD { SEQ_FRONT t }
  | SEQ_BACK t = terms PERIOD { SEQ_BACK t }
  | R_UNITARY1 PERIOD { R_UNITARY1 }

terms:
  | v = ID                                { Var v }
  | LPAREN t1 = terms RPAREN              { t1 }
  | TYPE                                  { Type }
  | PROP                                  { Prop }
  | QVLIST                                { QVList }
  | OPTPAIR LBRACK t = terms RBRACK       { OptPair t }
  | CTYPE                                 { CType }
  | CVAR LBRACK t = terms RBRACK          { CVar t }
  | QREG LBRACK t = terms RBRACK          { QReg t }
  | PROG                                  { Prog }
  | CASSN                                 { CAssn }
  | QASSN                                 { QAssn }
  | CQASSN                                          { CQAssn }
  | BIT                                             { Bit }
  | CTERM LBRACK t = terms RBRACK                   { CTerm t }
  | STYPE                                           { SType }
  | OTYPE LBRACK t1 = terms COMMA t2 = terms RBRACK { OType (t1, t2) }
  | DTYPE LBRACK t1 = terms COMMA t2 = terms RBRACK { DType (t1, t2) }

  | t1 = terms STAR t2 = terms { Star (t1, t2) }
  | v = ID AT1 { At1 v }
  | v = ID AT2 { At2 v }

  | LPAREN t1 = terms COMMA t2 = terms RPAREN { Pair (t1, t2) }
  | LANGLE t1 = terms COMMA t2 = terms RANGLE { AnglePair (t1, t2) }
  | LBRACK qrls = qreg_list RBRACK { QVListTerm qrls }
  | t1 = terms UNDERSCORE t2 = terms COMMA t3 = terms { Subscript (t1, t2, t3) }

  | t = bitterm   { BitTerm t }
  // | c = cassn { CAssnTerm c }
  | op = opt      { OptTerm op }
  | cq = cqassn   { CQAssnTerm cq }
  | s = stmt_seq  { ProgTerm s }
  | p = props     { PropTerm p }

qreg:
  | v = ID      { Var v }
  | v = ID AT1  { At1 v }
  | v = ID AT2  { At2 v }

qreg_list:
  | qr = qreg COMMA tls = qreg_list { qr :: tls }
  | qr = qreg                       { [qr] }

bitterm:
  | TRUE                        { True }
  | FALSE                       { False }
  | t1 = terms EQEQ t2 = terms  { Eq {t1; t2} }

// cassn:
//   | TRUE { True }
//   | FALSE { False }

opt:
  | ONEO LBRACK t       = terms RBRACK    { OneO t }
  | ZEROO LBRACK t1     = terms COMMA t2 = terms RBRACK { ZeroO {t1; t2} }
  | o1 = terms PLUS o2  = terms      { Add {o1; o2} }

cqassn:
  | psi = terms MAPSTO p = terms    { Fiber {psi; p} }
  | cq1 = terms PLUSCQ cq2 = terms  { Add {cq1; cq2} }
  | u = terms AT cq = terms         { UApply {u; cq} }

stmt_seq:
  | s = stmt ss = stmt_seq          { s :: ss }
  | s = stmt                        { SingleCmd s }

stmt:
  | SKIP                                                        { Skip }
  | id = ID ASSIGN t = terms                                    { Assign {x=id; t=t} }
  | id = ID RNDARROW t = terms                                  { PAssign {x=id; t=t} }
  | INIT q           = terms                                    { InitQubit q }
  | UNITARY_PROG u_opt = terms qs = terms                       { Unitary {u_opt; qs} }
  | id = ID ASSIGN MEAS m_opt = terms qs = terms                { Meas {x=id; m_opt=m_opt; qs=qs} }
  | IF b = terms THEN s1 = terms ELSE s2 = terms END            { IfMeas {b; s1; s2} }
  | WHILE b    = terms DO s = terms END                         { WhileMeas {b; s} }


props:
  | PROP_UNITARY t = terms          { Unitary t }
  | PROP_POS t = terms              { Pos t }
  | PROP_PROJ t = terms             { Proj t }
  | PROP_MEAS t = terms             { Meas t }
  | LBRACE pre = terms RBRACE s1 = terms TILDE s2 = terms LBRACE post = terms RBRACE { Judgement {pre; s1; s2; post} }
  | t1 = terms EQ t2 = terms        { Eq {t1; t2} }
  | t1 = terms LEQ t2 = terms       { Leq {t1; t2} }
