
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
  | Refl
  | Destruct of string
  | Intro of string
  | Choose of int
  | Split
  | ByLean
  | Simpl
  | Rewrite_L2R of terms
  | Rewrite_R2L of terms

  | R_SKIP
  | R_SEQ of int * int * terms
  | R_INITQ
  | R_UNITARY
  | R_MEAS_SAMPLE of bool

  | JUDGE_SWAP
  | CQ_ENTAIL
  | DIRAC
  | SIMPL_ENTAIL


and terms = 
  | Symbol of string
  | Fun of {head: string; args: terms list}
  | Opaque



(* The reserved term symbols *)

let _type = "Type"
let _forall = "FORALL"
let _fun = "FUN"
let _apply = "APPLY"

let _ctype = "CTYPE"
let _cvar = "CVAR"
let _cterm = "CTERM"
let _pdist = "PDIST"  (* Probability distribution. *)
let _set = "SET"
let _bit = "BIT"

let _qvlist = "QVLIST"
let _optpair = "OPTPAIR"
let _qreg = "QREG"
let _stype = "STYPE"
let _ktype = "KTYPE"
let _btype = "BTYPE"
let _otype = "OTYPE"
let _dtype = "DTYPE"

(** The type for a single program statement. *)
let _progstt = "PROGSTT"

(** The type for programs. *)
let _prog = "PROG"
let _cqproj = "CQPROJ"
let _assn = "ASSN"

let _pair = "PAIR"
let _list = "LIST"

let _ket = "KET"
let _bra = "BRA"
let _adj = "ADJ"
let _zeroo = "ZEROO"
let _oneo = "ONEO"
let _plus = "PLUS"
let _sum = "SUM"
let _tr = "tr"

let _uset = "USET"

let _subscript = "SUBSCRIPT"

let _true = "true"
let _false = "false"
let _eqeq = "EQEQ"
let _wedge = "WEDGE"
let _vee = "VEE"
let _not = "NOT"
let _imply = "IMPLY"

let _atat = "ATAT"

let _guarded = "GUARDED"

let _vbar = "VBAR"


(* and stmt_seq =
  | SingleCmd of stmt
  | (::) of stmt * stmt_seq

and stmt =
  | Skip
  | Assign of {x: string; t: terms}
  | PAssign of {x: string; t: terms}
  | InitQubit of      terms
  | Unitary of        {u_opt: terms; qs: terms}
  | Meas of           {x: string; m_opt: terms; qs: terms}
  | IfMeas of         {b: terms; s1: terms; s2: terms}
  | WhileMeas of      {b: terms; s: terms} *)

let _seq = "SEQ"
let _skip = "SKIP"
let _assign = "ASSIGN"
let _passign = "PASSIGN"
let _init_qubit = "INITQUBIT"
let _unitary = "UNITARY"
let _meas = "MEAS"
let _if = "IF"
let _while = "WHILE"

let _eq = "EQ"
let _inspace = "INSPACE"
let _entailment = "ENTAILMENT"
let _judgement = "JUDGEMENT"

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

  _pair;

  _ket;
  _bra;
  _adj;
  _zeroo;
  _oneo;
  _plus;
  _sum;
  _tr;

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
  _judgement;]



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


type envItem =
  | Assumption of {name: string; t: terms}
  | Definition of {name: string; t: terms; e: terms}

(* The well-formed environment and context *)
type wf_ctx = {
  env: envItem list; 
  ctx: envItem list
}