(*************************************************************************)
(* The file to hold the Lean_ast representation                          *)
(* All the code to be generated as a LEAN4 file is represented as an AST *)
(* OCAML syntax is converted into LEAN4 AST by the `by_lean` tactic      *)
(* Then, LEAN4 AST is utilized for code generation of the LEAN4 code     *)
(*************************************************************************)

(* Define the representation of LEAN4 as an AST *)
type ident = string

type expr =
  | Var           of ident
  | App           of expr * expr
  | Arrow         of expr * expr
  | StructInst    of (ident * expr) list
  | Vector        of expr list
  | BinOp         of string * expr * expr
  | UnOp          of string * expr
  | LitInt        of int
  | LitFloat      of string
  | LitString     of string
  | Annotation    of expr   * expr
  | Lambda        of ident  * expr * expr
  | Forall        of ident  * expr * expr
  | Prod          of expr list
  | GenericRepr   of string
  | Hole
  | Sorry
  | Type

type binder_style =
  | Explicit  (* Represents () *)
  | Implicit  (* Represents {} *)
  | Instance  (* Represents [] *)

type binder = {
  name    : ident;
  type_b  : expr;
  style   : binder_style;
}

type decl =
  | Import      of ident
  | Variable    of binder list
  | Notation    of {
      is_local    : bool;
      symbol      : string;
      definition  : expr;
    }
  | Definition of {
      is_noncomputable  : bool;
      name              : ident;
      params            : binder list;
      type_v            : expr option;
      body              : expr;
    }
  | Lemma of {
      name    : ident;
      params  : binder list;
      type_b  : expr;
      body    : expr;
    }
  | DocComment of string * decl

type lean_file = {
  header        : string option;
  imports       : decl list;
  declarations  : decl list;
}