(*************************************************************************)
(* The file to hold the Lean_ast representation                          *)
(* All the code to be generated as a CoqQ file is represented as an AST *)
(* OCAML syntax is converted into CoqQ AST by the `by_lean` tactic      *)
(* Then, CoqQ AST is utilized for code generation of the CoqQ code     *)
(*************************************************************************)

(** Define the representation of CoqQ as an AST **)
type ident = string
  [@@deriving show]

(** The different kinds of literal values. **)
type literal =
  | LitInt        of int
  | LitBool       of bool
  | LitFloat      of string
  | LitString     of string
  [@@deriving show]

(* The different kinds of expressions in CoqQ. *)
type expr =
  | Var           of ident
  | App           of expr * expr
  | Forall        of ident * expr * expr
  | LetIn         of ident * expr * expr
  | BinOp         of string * expr * expr
  | UnOp          of string * expr
  | Arrow         of expr * expr
  | Lit           of literal
  | Annotation    of expr   * expr
  | GenericRepr   of string
  | Abort
  
  (* Custom notation for CoqQ *)
  | Tick          of expr
  | DoubleTick    of expr
  | KetBra        of expr * expr
  | Trace         of expr * expr
  | Adjoint       of expr
  | LabelDirac    of expr * (expr list)
  [@@deriving show]

type binder = {
  name    : ident;
  type_b  : expr;
}[@@deriving show]

type decl =
  | Import      of ident
  | Variable    of binder list
  | Definition  of {
      name              : ident;
      params            : binder list;
      type_v            : expr option;
      body              : expr;
    }
  | Hypothesis  of {
      name  : ident;
      type_b  : expr option;
    }
  | Lemma of {
      name    : ident;
      params  : binder list;
      type_b  : expr;
      body    : expr;
    }
  | DocComment of string * decl
[@@deriving show]

type coqQ_file = {
  header        : string option;
  imports       : decl list;
  declarations  : decl list;
}[@@deriving show]
