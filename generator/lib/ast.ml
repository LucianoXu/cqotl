
type qreg = string list

(* qWhile Grammar:
  Seq ::= S1 S2 ... Sn    (n >= 1)
  S ::= skip ;
    |   q := |0> ;
    |   U[q_reg] ;
    |   if M[q_reg] then Seq1 else Seq2 end
    |   while M[q_reg] do Seq end
*)

type command =
  | Def of {x : string; t : types; e : terms}
  | DefWithoutType of {x : string; e : terms}
  | Var of {x : string; t : types}
  | Check of terms
  | Show of string
  | ShowAll
  | Undo
  | Pause
  (* For defining hypotheses *)
  | Assume of {x : string; p : props}
  (* for interactive proof *)
  | Prove of {x : string; p : props}
  | Tactic of tactic
  | QED

and tactic =
  | Sorry

  (* The two sided rules *)
  | R_SKIP

and types =
  | QVar
  | QReg of int
  | Opt of int
  | LOpt
  | MeasOpt
  | Program


and props =
  | Unitary of terms
  | Assn of terms
  | Meas of terms
  | Judgement of {
    pre: terms;
    s1 : terms;
    s2 : terms;
    post : terms;
  } 
  | Eq of {t1: terms; t2: terms}

and terms =
  | Var of string

  | QRegTerm of qreg

  | OptTerm of opt

  | LOptTerm of lopt

  | MeasOpt of {m1 : terms; m2 : terms}

  | Stmt of stmt_seq

and opt =
  | Add of {o1: terms; o2: terms} (* It seems that use opt as the type is the best choice. It enables direct decomposition to operator arguments. *)
  (* syntax for operators are omitted *)

and lopt = 
  | Pair of {opt: terms; qs: qreg}
  (* other syntax are omitted *)


(* A Statement Sequence *)
and stmt_seq =
  | SingleCmd of stmt
  | (::) of stmt * stmt_seq

(* Single Statements *)
and stmt =
  | Skip
  | InitQubit of      string
  | Unitary of   {u_opt: terms; qs: qreg}
  | IfMeas of         {m_opt: terms; s1: terms; s2: terms}
  | WhileMeas of      {m_opt: terms; s: terms}
