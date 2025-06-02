(****************************************************************************)
(* This file holds the code to print/create a LEAN4 file from the LEAN4 AST *)
(****************************************************************************)
(* open Lean_ast *)

open Lean_ast

let rec expr_to_string = function
  | Var x         -> x
  | App (f, x)    ->
    "(" ^ expr_to_string f ^ " " ^ expr_to_string x ^ ")"
  | Arrow (a, b)  ->
    "(" ^ expr_to_string a ^ " → " ^ expr_to_string b ^ ")"
  | LitInt n      -> string_of_int n
  | LitFloat s    -> s
  | LitString s   -> "\"" ^ s ^ "\""
  | GenericRepr s -> s
  | Type          -> "Type*"
  | Sorry         -> "sorry"
  | Hole          -> "_"
  | _             -> "Not implemented yet."

let binder_to_string (b : binder) : string        =
  "(" ^ b.name ^ " : " ^ expr_to_string b.type_b ^ ")"

let binders_to_string (bs : binder list) : string =
  String.concat " " (List.map binder_to_string bs)

let decl_to_string (d : decl) : string      =
  match d with
  | Import name ->
    "import " ^ name
  | Variable bs ->
    "variable " ^ binders_to_string bs
  | Definition { is_noncomputable; name; params; type_v; body } ->
    let prefix      = if is_noncomputable then "noncomputable def " else "def " 
      in
    let params_str  = binders_to_string params 
      in
    let type_str    = match type_v with
                        | Some ty   -> " : " ^ expr_to_string ty
                        | None      -> ""
      in
      prefix ^ name ^ " " ^ params_str ^ type_str ^ " := " ^ expr_to_string body
  | Lemma { name; params; type_b; body } ->
    "lemma " ^ name ^ " " ^ binders_to_string params ^
    " : " ^ expr_to_string type_b ^ " := " ^ expr_to_string body
  | Notation _ ->
      "-- Notation declaration not implemented yet."
  | DocComment (_, _) ->
    "-- Doc comment not implemented yet."
  
let lean_ast_to_lean_file (file : lean_file) : string =
  let header_str = 
    match file.header with
      | Some h -> h ^ "\n\n"
      | None -> ""
  in
  let imports_str = String.concat "\n" (List.map decl_to_string file.imports)         in
  let decls_str   = String.concat "\n\n" (List.map decl_to_string file.declarations)  in
  header_str ^ imports_str ^ "\n\n" ^ decls_str