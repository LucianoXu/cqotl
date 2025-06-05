%{
  open Ast
  open Ast_transform
%}

%token <string> ID
%token <int> NUM

(* character symbols *)
%token VEE WEDGE LONGARROW ARROW DARROW COLON COMMA PERIOD MAPSTO VDASH RNDARROW LARROW ASSIGN SEMICOLON LBRACK RBRACK LEQ EQEQ EQ TILDE LBRACE RBRACE PLUS LPAREN RPAREN STAR ATAT AT HASH VBAR RANGLE LANGLE ADJ UNDERSCORE

(* token for commands *)
%token DEF VAR CHECK SHOW SHOWALL UNDO PAUSE PROVE QED

(* token for tactics *)
%token SORRY EXPAND REFL DESTRUCT INTRO CHOOSE SPLIT BYLEAN SIMPL REWRITE RWRULE
%token R_PRE R_POST R_SKIP R_SEQ R_ASSIGN R_INITQ R_UNITARY R_IF R_WHILE_WHILE R_MEAS_MEAS R_MEAS_SAMPLE SWITCH_ID SWITCH_SWAP
%token JUDGE_SWAP CQ_ENTAIL DIRAC SIMPL_ENTAIL

%token FORALL FUN TYPE TR

(* token for Dirac notation *)
%token ONEO ZEROO

(* token for programs *)
%token SKIP INIT UNITARY_PROG MEAS IF THEN ELSE WHILE DO END

%token EOF

(* token for unexpected input *)
%token UNEXPECTED


/* -- precedence table -- */

%nonassoc FORALL FUN
%nonassoc EQ LEQ
%nonassoc VBAR
%nonassoc MAPSTO 
%left VEE
%left WEDGE
%right ARROW
%nonassoc TILDE LBRACE RBRACE
%nonassoc SEMICOLON
%nonassoc SKIP ASSIGN RNDARROW INIT UNITARY_PROG MEAS IF WHILE
%nonassoc EQEQ
%left PLUS
%left STAR
%left AT ATAT
%nonassoc ADJ
%nonassoc UNDERSCORE
%nonassoc LPAREN RPAREN
/**************************/

%start command_list terms_eof rewriting_rule_eof
%type <Ast.command list> command_list
%type <Ast.terms> terms_eof
%type <Ast.rewriting_rule> rewriting_rule_eof

%%

command_list:
  | EOF { [] }
  | c = command cl = command_list { c :: cl }

terms_eof:
  | t = terms EOF { t }

rewriting_rule_eof:
  (* Note that variable names are prefixed by '$' *)
  | r = rewriting_rule EOF { r }

rewriting_rule:
  | t1 = terms LONGARROW t2 = terms { rwrule_fresh_name {lhs=t1; rhs=t2; typings =[]} }
  | ts = typings VDASH t1 = terms LONGARROW t2 = terms { rwrule_fresh_name {lhs=t1; rhs=t2; typings = ts} }

typings:
  | t = terms COLON t2 = terms { [(t, t2)] }
  | t = terms COLON t2 = terms COMMA ts = typings { (t, t2) :: ts }

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
  | EXPAND v = ID PERIOD { Expand v }
  | REFL PERIOD { Refl }
  | DESTRUCT v = ID PERIOD { Destruct v }
  | INTRO v = ID PERIOD { Intro v}
  | CHOOSE n = NUM PERIOD { Choose n }
  | SPLIT PERIOD { Split }
  | BYLEAN PERIOD { ByLean }
  | SIMPL PERIOD { Simpl }
  | REWRITE t = terms PERIOD { Rewrite_L2R t }
  | REWRITE LARROW t = terms PERIOD { Rewrite_R2L t }
  | RWRULE r = rewriting_rule PERIOD { RWRULE r }

  | R_PRE pre = terms PERIOD { R_PRE pre }
  | R_POST post = terms PERIOD { R_POST post }
  | R_SKIP PERIOD { R_SKIP }
  | R_SEQ n1 = NUM n2 = NUM t = terms PERIOD { R_SEQ (n1, n2, t) }
  | R_ASSIGN PERIOD { R_ASSIGN }
  | R_INITQ PERIOD { R_INITQ }
  | R_UNITARY PERIOD { R_UNITARY }
  | R_IF qs = terms PERIOD { R_IF qs }
  | R_WHILE_WHILE qs = terms phi = terms PERIOD { R_WHILE_WHILE (qs, phi) }
  | R_MEAS_MEAS SWITCH_ID PERIOD { R_MEAS_MEAS true }
  | R_MEAS_MEAS SWITCH_SWAP PERIOD { R_MEAS_MEAS false }
  | R_MEAS_SAMPLE SWITCH_ID PERIOD { R_MEAS_SAMPLE true }
  | R_MEAS_SAMPLE SWITCH_SWAP PERIOD { R_MEAS_SAMPLE false }

  | JUDGE_SWAP PERIOD { JUDGE_SWAP }
  | CQ_ENTAIL PERIOD { CQ_ENTAIL }
  | DIRAC PERIOD { DIRAC }
  | SIMPL_ENTAIL PERIOD { SIMPL_ENTAIL }

// qvlist :
//   | q = ID { [q] }
//   | q = ID qs = qvlist { q :: qs }

terms:
  | LPAREN t1 = terms RPAREN { t1 }

  | v = ID { Symbol v }
  | head = ID LBRACK args = termargs RBRACK { Fun {head; args} }

  | TYPE { Symbol _type }
  | FORALL LPAREN x = ID COLON t1 = terms RPAREN COMMA t2 = terms { Fun {head=_forall; args=[Symbol x; t1; t2]} }
  | FUN LPAREN x = ID COLON t = terms RPAREN DARROW e = terms { Fun {head=_fun; args=[Symbol x; t; e]} }
  | f = terms AT t = terms { Fun {head=_apply; args=[f; t]} }

  (* star *)
  | t1 = terms STAR t2 = terms { Fun {head=_star; args=[t1; t2]} }

  (* pair *)
  | LPAREN t1 = terms COMMA t2 = terms RPAREN { Fun {head=_pair; args=[t1; t2]} }
  | LBRACK ts = termargs RBRACK { Fun {head=_list; args=ts} }

  (* 0O[T] or 0O[T1, T2] *)
  | VBAR t = terms RANGLE { Fun {head=_ket; args=[t]} }
  | LANGLE t = terms VBAR { Fun {head=_bra; args=[t]} }
  | t = terms ADJ { Fun {head=_adj; args=[t]} }

  | ZEROO LBRACK t = terms RBRACK { Fun {head=_zeroo; args=[t; t]} }
  | ZEROO LBRACK t1 = terms COMMA t2 = terms RBRACK { Fun {head=_zeroo; args=[t1; t2]} }
  | ONEO LBRACK t = terms RBRACK { Fun {head=_oneo; args=[t]} }

  | t1 = terms PLUS t2 = terms { Fun {head=_plus; args=[t1; t2]} }

  (* labelled trace *)
  | TR LBRACK t = terms RBRACK { Fun {head=_tr; args=[t]} }
  | TR UNDERSCORE q = terms LPAREN t = terms RPAREN  { Fun {head=_tr; args = [q; t] } } 

  | t1 = terms EQEQ t2 = terms { Fun {head=_eqeq; args=[t1; t2]} }
  | t1 = terms WEDGE t2 = terms { Fun {head=_wedge; args=[t1; t2]} }
  | t1 = terms VEE t2 = terms { Fun {head=_vee; args=[t1; t2]} }
  | TILDE t = terms { Fun {head=_not; args=[t]} }
  | t1 = terms ARROW t2 = terms { Fun {head=_imply; args=[t1; t2]} }

  | t1 = terms UNDERSCORE t2 = terms { Fun {head=_subscript; args=[t1; t2]} }

  | t1 = terms MAPSTO t2 = terms { Fun {head=_guarded; args=[t1; t2]} }

  | t1 = terms ATAT t2 = terms { Fun {head=_atat; args=[t1; t2]} }
  
  | t1 = terms VBAR t2 = terms { Fun {head=_vbar; args=[t1; t2]}}

  | t1 = terms EQ t2 = terms { Fun {head=_eq; args=[t1; t2]} }
  | t1 = terms LEQ t2 = terms { Fun {head=_entailment; args=[t1; t2]} }

  | LBRACE pre = terms RBRACE s1 = terms TILDE s2 = terms LBRACE post = terms RBRACE
    { Fun {head=_judgement; args=[pre; s1; s2; post]} }

  | LPAREN t1 = terms COMMA t2 = terms HASH COMMA t3 = terms RPAREN
    { Fun {head=_qcoupling; args=[t1; t2; t3]} }


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
  