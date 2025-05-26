%{
  open Ast
%}

%token <string> ID
%token <int> NUM

(* character symbols *)
%token VEE WEDGE ARROW DARROW AT1 AT2 COLON COMMA PERIOD MAPSTO PLUSCQ RNDARROW ASSIGN STARASSIGN KET0 SEMICOLON LBRACK RBRACK LEQ EQEQ EQ TILDE LBRACE RBRACE PLUS LPAREN RPAREN STAR AT VBAR RANGLE LANGLE ADJ

(* token for commands *)
%token DEF VAR CHECK SHOW SHOWALL UNDO PAUSE PROVE QED

(* token for tactics *)
%token SORRY CHOOSE INTRO BYLEAN SIMPL
%token R_SKIP SEQ_FRONT SEQ_BACK R_UNITARY1

%token FORALL FUN TYPE PROP QVLIST OPTPAIR CTYPE CVAR QREG PROG CASSN QASSN CQASSN BIT CTERM STYPE OTYPE DTYPE

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

%nonassoc FORALL FUN
%left VEE
%left WEDGE
%nonassoc MAPSTO 
%right ARROW
%nonassoc TILDE LBRACE RBRACE
%nonassoc SEMICOLON
%nonassoc SKIP ASSIGN RNDARROW INIT UNITARY_PROG MEAS IF WHILE
%left STAR
%nonassoc EQEQ EQ LEQ
%left PLUS
%left AT
%nonassoc LPAREN RPAREN
/**************************/

%start command_list
%type <Ast.command list> command_list

%%



// terms:
//   | v = ID { Var v }

//   | LPAREN t1 = terms RPAREN { t1 }

//   | FORALL LPAREN v = ID COLON t = terms RPAREN COMMA t2 = terms { Forall {x=v; t; t'=t2} }
//   | FUN LPAREN v = ID COLON t = terms RPAREN DARROW e = terms { Fun {x=v; t; e} }
//   // | f = terms t = terms { Apply (f, t) }
//   | TYPE { Type }
//   | PROP { Prop }
//   | QVLIST { QVList }
//   | OPTPAIR LBRACK t = terms RBRACK { OptPair t }
//   | CTYPE { CType }
//   | CVAR LBRACK t = terms RBRACK { CVar t }
//   | QREG LBRACK t = terms RBRACK { QReg t }
//   | PROG { Prog }
//   | CASSN { CAssn }
//   | QASSN { QAssn }
//   | CQASSN { CQAssn }

//   | BIT { Bit }

//   | CTERM LBRACK t = terms RBRACK { CTerm t }
//   | STYPE { SType }
//   | OTYPE LBRACK t1 = terms COMMA t2 = terms RBRACK { OType (t1, t2) }
//   | DTYPE LBRACK t1 = terms COMMA t2 = terms RBRACK { DType (t1, t2) }

//   | t1 = terms STAR t2 = terms { Star (t1, t2) }
//   | v = ID AT1 { At1 v }
//   | v = ID AT2 { At2 v }

//   | LPAREN t1 = terms COMMA t2 = terms RPAREN { Pair (t1, t2) }
//   | LANGLE t1 = terms COMMA t2 = terms RANGLE { AnglePair (t1, t2) }
//   | LBRACK qrls = qreg_list RBRACK { QVListTerm qrls }
//   | t1 = terms UNDERSCORE t2 = terms COMMA t3 = terms { Subscript (t1, t2, t3) }

//   | t = bitterm   { BitTerm t }
//   // | c = cassn { CAssnTerm c }
//   | op = opt      { OptTerm op }
//   | cq = cqassn   { CQAssnTerm cq }
//   | s = stmt_seq  { ProgTerm s }
//   | p = props     { PropTerm p }

// qreg:
//   | v = ID      { Var v }
//   | v = ID AT1  { At1 v }
//   | v = ID AT2  { At2 v }

// qreg_list:
//   | qr = qreg COMMA tls = qreg_list { qr :: tls }
//   | qr = qreg                       { [qr] }

// bitterm:
//   | TRUE                        { True }
//   | FALSE                       { False }
//   | t1 = terms EQEQ t2 = terms  { Eq {t1; t2} }

// // cassn:
// //   | TRUE { True }
// //   | FALSE { False }

// opt:
//   | ONEO LBRACK t       = terms RBRACK    { OneO t }
//   | ZEROO LBRACK t1     = terms COMMA t2 = terms RBRACK { ZeroO {t1; t2} }
//   | o1 = terms PLUS o2  = terms      { Add {o1; o2} }

// cqassn:
//   | psi = terms MAPSTO p = terms    { Fiber {psi; p} }
//   | cq1 = terms PLUSCQ cq2 = terms  { Add {cq1; cq2} }
//   | u = terms AT cq = terms         { UApply {u; cq} }

// stmt_seq:
//   | s = stmt ss = stmt_seq          { s :: ss }
//   | s = stmt                        { SingleCmd s }

// stmt:
//   | SKIP                                                        { Skip }
//   | id = ID ASSIGN t = terms                                    { Assign {x=id; t=t} }
//   | id = ID RNDARROW t = terms                                  { PAssign {x=id; t=t} }
//   | INIT q           = terms                                    { InitQubit q }
//   | UNITARY_PROG u_opt = terms qs = terms                       { Unitary {u_opt; qs} }
//   | id = ID ASSIGN MEAS m_opt = terms qs = terms                { Meas {x=id; m_opt=m_opt; qs=qs} }
//   | IF b = terms THEN s1 = terms ELSE s2 = terms END            { IfMeas {b; s1; s2} }
//   | WHILE b    = terms DO s = terms END                         { WhileMeas {b; s} }


// props:
//   | PROP_UNITARY t = terms          { Unitary t }
//   | PROP_POS t = terms              { Pos t }
//   | PROP_PROJ t = terms             { Proj t }
//   | PROP_MEAS t = terms             { Meas t }
//   | LBRACE pre = terms RBRACE s1 = terms TILDE s2 = terms LBRACE post = terms RBRACE { Judgement {pre; s1; s2; post} }
//   | t1 = terms EQ t2 = terms        { Eq {t1; t2} }
//   | t1 = terms LEQ t2 = terms       { Leq {t1; t2} }



command_list:
  | EOF { [] }
  | c = command cl = command_list { c :: cl }

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
  | INTRO v = ID PERIOD { Intro v}
  | CHOOSE n = NUM PERIOD { Choose n }
  | BYLEAN PERIOD { ByLean }
  | SIMPL PERIOD { Simpl }
  | R_SKIP PERIOD { R_SKIP }
  // | SEQ_FRONT t = terms PERIOD { SEQ_FRONT t }
  // | SEQ_BACK t = terms PERIOD { SEQ_BACK t }
  // | R_UNITARY1 PERIOD { R_UNITARY1 }

terms:
  | LPAREN t1 = terms RPAREN { t1 }

  | v = ID { Symbol v }
  | head = ID LBRACK args = termargs RBRACK { Fun {head; args} }

  | TYPE { Symbol _type }
  | FORALL LPAREN x = ID COLON t1 = terms RPAREN COMMA t2 = terms { Fun {head=_forall; args=[Symbol x; t1; t2]} }
  | FUN LPAREN x = ID COLON t = terms RPAREN DARROW e = terms { Fun {head=_fun; args=[Symbol x; t; e]} }
  | f = terms AT t = terms { Fun {head=_apply; args=[f; t]} }

  (* pair *)
  | LPAREN t1 = terms COMMA t2 = terms RPAREN { Fun {head=_pair; args=[t1; t2]} }

  (* 0O[T] or 0O[T1, T2] *)
  | VBAR t = terms RANGLE { Fun {head=_ket; args=[t]} }
  | LANGLE t = terms VBAR { Fun {head=_bra; args=[t]} }
  | t = terms ADJ { Fun {head=_adj; args=[t]} }

  | ZEROO LBRACK t = terms RBRACK { Fun {head=_zeroo; args=[t; t]} }
  | ZEROO LBRACK t1 = terms COMMA t2 = terms RBRACK { Fun {head=_zeroo; args=[t1; t2]} }
  | ONEO LBRACK t = terms RBRACK { Fun {head=_oneo; args=[t]} }

  | t1 = terms PLUS t2 = terms { Fun {head=_plus; args=[t1; t2]} }

  | t1 = terms EQEQ t2 = terms { Fun {head=_eqeq; args=[t1; t2]} }
  | t1 = terms WEDGE t2 = terms { Fun {head=_wedge; args=[t1; t2]} }
  | t1 = terms VEE t2 = terms { Fun {head=_vee; args=[t1; t2]} }
  | TILDE t = terms { Fun {head=_not; args=[t]} }
  | t1 = terms ARROW t2 = terms { Fun {head=_imply; args=[t1; t2]} }


  | t1 = terms EQ t2 = terms { Fun {head=_eq; args=[t1; t2]} }

  | LBRACE pre = terms RBRACE s1 = terms TILDE s2 = terms LBRACE post = terms RBRACE
    { Fun {head=_judgement; args=[pre; s1; s2; post]} }


  | SKIP                                                        { Symbol _skip }
  | id = ID ASSIGN t = terms                                    { Fun {head=_assign; args=[Symbol id; t]} }
  | id = ID RNDARROW t = terms                                  { Fun {head=_passign; args=[Symbol id; t]} }
  | INIT q           = terms                                    { Fun {head=_init_qubit; args=[q]} }
  | UNITARY_PROG u_opt = terms qs = terms                       { Fun {head=_unitary; args=[u_opt; qs]} }
  | id = ID ASSIGN MEAS m_opt = terms qs = terms                { Fun {head=_meas; args=[Symbol id; m_opt; qs]} }
  | IF b = terms THEN s1 = terms ELSE s2 = terms END            { Fun {head=_if; args=[b; s1; s2]} }
  | WHILE b    = terms DO s = terms END                         { Fun {head=_while; args=[b; s]} }
  | stmts = stmtseq                                             { Fun {head=_seq; args=stmts} }


termargs:
  | t = terms { [t] }
  | t = terms COMMA ts = termargs { t :: ts }

stmtseq:
  | t = terms SEMICOLON { [t] }
  | t = terms SEMICOLON ts = stmtseq { t :: ts }
  