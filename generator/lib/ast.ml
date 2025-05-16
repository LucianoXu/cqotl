
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
  | Choose of int

  (* The two sided rules *)
  | R_SKIP
  | SEQ_FRONT of terms
  | SEQ_BACK of terms
  | R_UNITARY1

and terms = 
  | Var of string

  (* Forbid variables for these three types. *)
  | Type
  | Prop
  | QVList
  | OptPair of terms

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
  | At1 of string
  | At2 of string

  | Pair of terms * terms
  | AnglePair of terms * terms
  | QVListTerm of terms list     (* A set of (constant) quantum variable *)
  | Subscript of terms * terms * terms

  | BitTerm of bitterm

  | OptTerm of opt
  | CQAssnTerm of cqassn
  | ProgTerm of stmt_seq
  | PropTerm of props

  | ProofTerm         (* the constant opaque proof term *)

and bitterm =
  | True 
  | False
  | Eq of {t1: terms; t2: terms}

and opt =
  | OneO of terms
  | ZeroO of {t1: terms; t2: terms}
  | Add of {o1: terms; o2: terms}
  (* syntax for operators are omitted *)

and cqassn =
  | Fiber of {psi: terms; p: terms}
  | Add of {cq1: terms; cq2: terms}
  | UApply of {u: terms; cq: terms}

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
  | Meas of           {x: string; m_opt: terms; qs: terms}
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
  | Leq of {t1: terms; t2: terms}


let get_front_stmt (s: stmt_seq) : (stmt * stmt_seq) =
  match s with
  | SingleCmd s -> (s, SingleCmd Skip)
  | (s1 :: s2) -> (s1, s2)

let rec stmt_seq_concat (s1: stmt_seq) (s2: stmt_seq) : stmt_seq =
  match s1 with
  | SingleCmd s -> s :: s2
  | (::) (hd, tl) -> hd :: (stmt_seq_concat tl s2)

let rec get_back_stmt (s: stmt_seq) : (stmt * stmt_seq) =
  match s with
  | SingleCmd s -> (s, SingleCmd Skip)
  | (s1 :: SingleCmd s2) -> (s2, SingleCmd s1)      
  | (s1 :: s2) -> 
      let (end_stmt, remain) = get_back_stmt s2 in
      (end_stmt, s1 :: remain)