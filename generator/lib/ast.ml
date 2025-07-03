
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
  | Synthesize of {t : terms}
  [@@deriving show]

and tactic =
  | Sorry
  | Expand        of string
  | Refl
  | Destruct  of string
  | Case      of terms
  | Intro     of string
  | Revert    of string
  | Apply     of terms
  | Choose    of int
  | Split
  | ByLean
  | Simpl
  | Rewrite_L2R of terms
  | Rewrite_R2L of terms
  | RWRULE of rewriting_rule
  | R_PRE of terms
  | R_POST of terms
  | R_SKIP
  | R_SEQ of int * int * terms
  | R_ASSIGN
  | R_INITQ
  | R_UNITARY
  | R_MEAS
  | R_IF of terms
  | R_WHILE of terms * terms
  | R_WHILE_WHILE of terms * terms
  | R_MEAS_MEAS of bool
  | R_MEAS_SAMPLE of bool
  | JUDGE_SWAP
  | CQ_ENTAIL
  | DIRAC
  | SIMPL_ENTAIL
  | ENTAIL_TRANS of terms
  | CYLINDER_EXT of terms
  [@@deriving show]

and terms = 
  | Symbol of string
  | Fun of {head: string; args: terms list}
  | Opaque
  [@@deriving show]

and rewriting_rule = {
  lhs: terms;  (* left-hand side of the rule *)
  rhs: terms;  (* right-hand side of the rule *)
  typings: (terms * terms) list;  (* optional typing information *)
} [@@deriving show]

type envItem =
  | Assumption of {name: string; t: terms}
  | Definition of {name: string; t: terms; e: terms}
  [@@deriving show]

type normal_frame = {
  env: envItem list;
}
[@@deriving show]

(* The environment for the whole proof *)
type proof_frame = {
  env       : envItem list;
  proof_name: string;
  proof_prop: terms;
  goals     : (envItem list * terms) list;
  lean_goals: (envItem list * terms) list;
}
[@@deriving show]

type frame = 
  | NormalFrame of normal_frame
  | ProofFrame  of proof_frame
[@@deriving show]

(** The prover. 
  Initially it has empty stack and the frame is described by empty_frame. *)
type prover = {
  mutable stack: frame list;  (* The new frames *)
}
[@@deriving show]
  
type tactic_result =
  | Success of frame
  | TacticError of string
  [@@deriving show]
  
type eval_result = 
  | Success
  | ProverError of string
  | Pause
  [@@deriving show]

type ('a, 'b) lean4Result   = Result of 'a | LeanTranslationError of 'b [@@deriving show]

(* The well-formed environment and context *)
type wf_ctx = {
  env         : envItem list; 
  ctx         : envItem list
}[@@deriving show]

type obligation_proof_frame = {
  env         : envItem list;
  context     : envItem list;
  goal        : terms;
}
[@@deriving show]

let (>>=) (res : ('a, 'b) lean4Result) (f : 'a -> ('c, 'b) lean4Result) : ('c, 'b) lean4Result =
  match res with
  | Result v                    -> f v
  | LeanTranslationError msg    -> LeanTranslationError msg

(** transformation type *)
type transform  = terms -> terms option [@@deriving show]

(** substitution type *)
type subst      = (string * terms) list [@@deriving show]

(* Type Definitions for the `typing.ml` *)

(* QVList Calculation *)
type termls_result =
  | TermList    of terms list
  | TermError   of string

type typing_result =
  | Type        of terms
  | TypeError   of string

(* The reserved term symbols *)

(* a trick: we use Type[Type[...]] to represent the typing hierarchy. *)
let _type     = "Type"
let _forall   = "FORALL"
let _fun      = "FUN"
let _apply    = "APPLY"

let _ctype    = "CType"
let _cvar     = "CVar"
let _cterm    = "CTerm"
let _pdist    = "PDist"   (* Probability distribution. *)
let _set      = "Set"
let _bit      = "bit"
let _int      = "int"     (* Integer type. *)
let _qvlist   = "QVList"
let _optpair  = "OptPair"
let _qreg     = "QReg"
let _stype    = "SType"
let _ktype    = "KType"
let _btype    = "BType"
let _otype    = "OType"
let _dtype    = "DType"

(** The type for a single program statement. *)
let _progstt  = "ProgStt"

(** The type for programs. *)
let _prog     = "Prog"
let _cqproj   = "CQProj"
let _assn     = "Assn"

let _star     = "STAR"
let _pair     = "PAIR"
let _list     = "LIST"

let _ket      = "KET"
let _bra      = "BRA"
let _adj      = "ADJ"
let _zeroo    = "ZEROO"
let _oneo     = "ONEO"
let _plus     = "PLUS"
let _sum      = "SUM"
let _tr       = "tr"

let _top      = "TOP"
let _bottom   = "BOT"

let _uset     = "USET"

let _subscript  = "SUBSCRIPT"

let _true       = "true"
let _false      = "false"
let _eqeq       = "EQEQ"
let _wedge      = "WEDGE"
let _vee        = "VEE"
let _not        = "NOT"
let _imply      = "IMPLY"

let _atat       = "ATAT"

let _guarded    = "GUARDED"

let _vbar       = "VBAR"

let _seq        = "SEQ"
let _skip       = "SKIP"
let _assign     = "ASSIGN"
let _passign    = "PASSIGN"
let _init_qubit = "INITQUBIT"
let _unitary    = "UNITARY"
let _meas       = "MEAS"
let _if         = "IF"
let _while      = "WHILE"

let _eq         = "EQ"
let _inspace    = "INSPACE"
let _entailment = "ENTAILMENT"

let _judgement  = "JUDGEMENT"


let _dopt = "DOpt" (* is density operator *)
let _popt = "POpt" (* is projector operator *)
let _uopt = "UOpt" (* is unitary operator *)
let _hopt = "HOpt" (* is Hermitian operator *)
let _projmeasoptpair = "ProjMeasOptPair" (* is a pair of projective operators *)
let _qcoupling  = "QCOUPLING"

let reserved_symbols = [
  _type;
  _forall;
  _fun;
  _apply;
  _ctype;
  _cvar;
  _cterm;
  _pdist;
  _set;
  _bit;
  _int;

  _qvlist;
  _optpair;

  _qreg;
  _stype;
  _otype;
  _dtype;

  _progstt;
  _prog;
  _cqproj;
  _assn;

  _star;
  _pair;
  _list;

  _ket;
  _bra;
  _adj;
  _zeroo;
  _oneo;
  _plus;
  _sum;
  _tr;
  _top;
  _bottom;

  _subscript;

  _uset;

  _true;
  _false;
  _eqeq;
  _wedge;
  _vee;
  _not;
  _imply;

  _atat;

  _vbar;

  _seq;
  _skip;
  _assign;
  _passign;
  _init_qubit;
  _unitary;
  _meas;
  _if;
  _while;
  
  _eq;
  _inspace;
  _entailment;
  _judgement;
  _dopt;
  _popt;
  _uopt;
  _hopt;
  _projmeasoptpair;

  _qcoupling;]

(** return the substitution result t\[v/x\] *)
let rec substitute (t : terms) (x: string) (v: terms) : terms =
  match t with
  | Symbol y -> if x = y then v else t
  | Fun {head; args=[Symbol x'; forall_t; forall_t']} when head = _forall && x' = x ->
      let new_forall_t = substitute forall_t x v in
      Fun {head; args=[Symbol x'; new_forall_t; forall_t']}

  | Fun {head; args=[Symbol x'; fun_t; fun_e]} when head = _fun && x' = x ->
      let new_fun_t = substitute fun_t x v in
      Fun {head; args=[Symbol x'; new_fun_t; fun_e]}

  | Fun {head; args} ->
      let args' = List.map (fun arg -> substitute arg x v) args in
      Fun {head; args = args'}

  | Opaque -> Opaque

(** Replace a subterm in the term t. *)
let rec replace (t : terms) (from_: terms) (to_: terms) : terms =
  if t = from_ then to_ else
  match t with
  | Symbol _ -> t
  | Fun {head; args} ->
      let args' = List.map (fun arg -> replace arg from_ to_) args in
      Fun {head; args = args'}
  | Opaque -> Opaque

(*************************************)
(** Get all the symbols in the term (function head are not counted). *)
let get_symbols (t : terms) : string list =
  let rec aux acc t =
    match t with
    | Symbol s -> s :: acc
    | Fun {head=_; args} ->
        List.fold_left aux acc args
    | Opaque -> acc
  in
  List.sort_uniq String.compare (aux [] t)

(** fresh symbol generator *)
let new_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    counter := id + 1;
    id

let fresh_name (symbol_ls: string list) (prefix : string) : string =
  if not (List.mem prefix symbol_ls) then 
    prefix
  else
    let rec find_fresh id =
      let candidate = prefix ^ string_of_int id in
      if List.mem candidate symbol_ls then
        find_fresh (id + 1)
      else
        candidate
    in
    find_fresh 0

(** Generates a fresh symbol name with a given prefix *)
let fresh_name_for_term (t : terms) (prefix : string) : string =
  let t_symbols = get_symbols t in
  fresh_name t_symbols prefix

let find_symbol (wfctx : wf_ctx) (x : string) : envItem option =
  let rec find_in_env env =
    match env with
    | [] -> None
    | Assumption {name; t} :: _ when name = x -> Some (Assumption {name; t})
    | Definition {name; t; e} :: _ when name = x -> Some (Definition {name; t; e})
    | _ :: rest -> find_in_env rest
  in
  match find_in_env wfctx.ctx with
  | Some item -> Some item
  | None -> find_in_env wfctx.env