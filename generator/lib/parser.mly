%{
  open Ast
  open Ast_transform
%}

%token <string> ID
%token <int> NUM

(* character symbols *)
%token VEE WEDGE LONGARROW ARROW DARROW AT1 AT2 COLON COMMA PERIOD MAPSTO VDASH PLUSCQ RNDARROW ASSIGN STARASSIGN KET0 SEMICOLON LBRACK RBRACK LEQ EQEQ EQ TILDE LBRACE RBRACE PLUS LPAREN RPAREN STAR AT VBAR RANGLE LANGLE ADJ UNDERSCORE

(* token for commands *)
%token DEF VAR CHECK SHOW SHOWALL UNDO PAUSE PROVE QED

(* token for tactics *)
%token SORRY INTRO CHOOSE SPLIT BYLEAN SIMPL
%token R_SKIP R_SEQ R_INITQ R_UNITARY1 
%token CQ_ENTAIL DELABEL

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
%nonassoc VBAR
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
%nonassoc UNDERSCORE
%nonassoc LPAREN RPAREN
/**************************/

%start command_list terms_eof rewriting_rule_eof
%type <Ast.command list> command_list
%type <Ast.terms> terms_eof
%type <Ast_transform.rewriting_rule> rewriting_rule_eof

%%

command_list:
  | EOF { [] }
  | c = command cl = command_list { c :: cl }

terms_eof:
  | t = terms EOF { t }

rewriting_rule_eof:
  (* Note that variable names are prefixed by '$' *)
  | t1 = terms LONGARROW t2 = terms EOF { rwrule_fresh_name {lhs=t1; rhs=t2; typings =[]} }
  | ts = typings VDASH t1 = terms LONGARROW t2 = terms EOF { rwrule_fresh_name {lhs=t1; rhs=t2; typings = ts} }

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
  | INTRO v = ID PERIOD { Intro v}
  | CHOOSE n = NUM PERIOD { Choose n }
  | SPLIT PERIOD { Split }
  | BYLEAN PERIOD { ByLean }
  | SIMPL PERIOD { Simpl }

  | R_SKIP PERIOD { R_SKIP }
  | R_SEQ n = NUM t = terms PERIOD { R_SEQ (n, t) }
  | R_INITQ PERIOD { R_INITQ }

  | CQ_ENTAIL PERIOD { CQ_ENTAIL }
  | DELABEL PERIOD { DELABEL }
  // | SEQ_FRONT t = terms PERIOD { SEQ_FRONT t }
  // | SEQ_BACK t = terms PERIOD { SEQ_BACK t }
  // | R_UNITARY1 PERIOD { R_UNITARY1 }

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

  | t1 = terms EQEQ t2 = terms { Fun {head=_eqeq; args=[t1; t2]} }
  | t1 = terms WEDGE t2 = terms { Fun {head=_wedge; args=[t1; t2]} }
  | t1 = terms VEE t2 = terms { Fun {head=_vee; args=[t1; t2]} }
  | TILDE t = terms { Fun {head=_not; args=[t]} }
  | t1 = terms ARROW t2 = terms { Fun {head=_imply; args=[t1; t2]} }

  | t1 = terms UNDERSCORE t2 = terms { Fun {head=_subscript; args=[t1; t2]} }

  | t1 = terms MAPSTO t2 = terms { Fun {head=_guarded; args=[t1; t2]} }
  
  | t1 = terms VBAR t2 = terms { Fun {head=_vbar; args=[t1; t2]}}

  | t1 = terms EQ t2 = terms { Fun {head=_eq; args=[t1; t2]} }
  | t1 = terms LEQ t2 = terms { Fun {head=_entailment; args=[t1; t2]} }

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
  