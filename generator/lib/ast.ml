
(* qWhile Grammar:
  Seq ::= S1 S2 ... Sn    (n >= 1)
  S ::= skip ;
    |   q := |0> ;
    |   U[q_reg] ;
    |   if M[q_reg] then Seq1 else Seq2 end
    |   while M[q_reg] do Seq end
*)

type command =
  | Def of {x : string; t : terms; e : terms}
  | DefWithoutType of {x : string; e : terms}
  | Var of {x : string; t : terms}
  | Check of terms
  | Show of string
  | ShowAll
  | Undo
  | Pause
  (* for interactive proof *)
  | Prove of {x : string; p : terms}
  | Tactic of tactic
  | QED

and tactic =
  | Sorry

  (* The two sided rules *)
  | R_SKIP

and terms = 
  | Var of string

  (* Forbid variables for these three types. *)
  | Type
  | Prop
  | QVList
  | OptPair

  | CType
  | CVar of terms
  | QReg of terms
  | Prog
  | CAssn
  | QAssn
  | CQAssn

  | Bit
  
  | CTerm of terms
  | SType
  | OType of terms * terms
  | DType of terms * terms

  | Star of terms * terms

  | Pair of terms * terms
  | AnglePair of terms * terms
  | QVListTerm of string list     (* A set of (constant) quantum variable *)
  | Subscript of terms * terms * terms

  | CAssnTerm of cassn
  | OptTerm of opt
  | CQAssnTerm of cqassn
  | ProgTerm of stmt_seq
  | PropTerm of props

  | ProofTerm         (* the constant opaque proof term *)

and cassn =
  | True
  | False

and opt =
  | Add of {o1: terms; o2: terms} (* It seems that use opt as the type is the best choice. It enables direct decomposition to operator arguments. *)
  (* syntax for operators are omitted *)

and cqassn =
  | Fiber of {psi: terms; p: terms}
  | Add of {cq1: terms; cq2: terms}

(* A Statement Sequence *)
and stmt_seq =
  | SingleCmd of stmt
  | (::) of stmt * stmt_seq

(* Single Statements *)
and stmt =
  | Skip
  | Assign of {x: string; t: terms}
  | PAssign of {x: string; t: terms}
  | InitQubit of      terms
  | Unitary of        {u_opt: terms; qs: terms}
  | Meas of           {x: string; m_opt: terms}
  | IfMeas of         {b: terms; s1: terms; s2: terms}
  | WhileMeas of      {b: terms; s: terms}


and props =
  | Unitary of terms
  | Pos of terms
  | Proj of terms
  | Meas of terms
  | Judgement of {
    pre: terms;
    s1 : terms;
    s2 : terms;
    post : terms;
  } 
  | Eq of {t1: terms; t2: terms}


(* the function to calculate the qvlist from the qreg term *)
let rec get_qvlist (qreg : terms) : string list =
  match qreg with
  | Var x -> [x]
  | Pair (t1, t2) -> List.concat [(get_qvlist t1); (get_qvlist t2)]
  | _ -> raise (Failure "Undefined get_qvlist")
