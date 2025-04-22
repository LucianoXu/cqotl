
(* This exception represents the error raised by incorrect use of the prover, such as syntax error or rule application error. This will be reported in the status. *)

type id                   = string
type qreg                 = id list

(* qWhile Grammar:
  Seq ::= S1 S2 ... Sn    (n >= 1)
  S ::= skip ;
    |   q := |0> ;
    |   U[q_reg] ;
    |   if M[q_reg] then Seq1 else Seq2 end
    |   while M[q_reg] do Seq end
*)

type command =
  | Def of {x : id; t : types; e : terms}
  | DefWithoutType of {x : id; e : terms}
  | Var of {x : id; t : types}
  | Check of terms
  | Show of id
  | ShowAll
  | Undo
  | Pause


and types =
  | QVar
  | QReg of int
  | Opt of int
  | LOpt
  | Assertion
  | Program
  | Judgement of {
    pre: terms;
    s1 : terms;
    s2 : terms;
    post : terms;
  } 

and terms =
  | Var of id

  | QRegTerm of qreg

  | OptTerm of opt

  | LOptTerm of lopt

  (* Note that assertions can only be constructed from labeled operators by proof. *)
  | Assertion of lopt 

  | Stmt of stmt_seq

  (* The opaque proof term. *)
  | Proof

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
  | InitQubit of      id
  | Unitary of   {u_opt: terms; qs: qreg}
  | IfMeas of         {m_opt: terms; s1: terms; s2: terms}
  | WhileMeas of      {m_opt: terms; s: terms}
