(****************************************************************************)
(* This file holds the code to print/create a LEAN4 file from the LEAN4 AST *)
(****************************************************************************)

open Lean_ast
open Printf

let rec expr_to_string expr =
    match expr with
    | Var x               -> x
    | LitInt n            -> string_of_int n
    | LitFloat s          -> s
    | LitString s         -> sprintf "%s" s
    | GenericRepr s       -> s
    | Type                -> "Type*"
    | Sorry               -> "sorry"
    | Hole                -> "_"
    | App (f, x)          -> sprintf "(%s %s)"    (expr_to_string f) (expr_to_string x)
    | Arrow (a, b)        -> sprintf "(%s → %s)"  (expr_to_string a) (expr_to_string b)
    | BinOp (op, l, r)    -> sprintf "(%s %s %s)" (expr_to_string l) op (expr_to_string r)
    | UnOp (op, e)        -> sprintf "(%s %s)" op (expr_to_string e)
    | Annotation (e, ty)  -> sprintf "(%s : %s)"  (expr_to_string e) (expr_to_string ty)
    | Prod elems          ->
        let elem_strings = List.map expr_to_string elems in
        sprintf "(%s)" (String.concat ", " elem_strings)
    | Lambda (name, ty, body) ->
        sprintf "fun (%s : %s) => %s" name (expr_to_string ty) (expr_to_string body)
    | StructInst fields   ->
        let field_strings = List.map (fun (name, value) -> sprintf "%s := %s" name (expr_to_string value)) fields in
        sprintf "{ %s }" (String.concat ", " field_strings)
    | Vector elems        ->
        let elem_strings  = List.map expr_to_string elems in
        sprintf "#[%s]" (String.concat ", " elem_strings)
  
  (* Bindings and Binder lists *)
  let binder_to_string (b : binder) : string          =
    let content = sprintf "%s : %s" b.name (expr_to_string b.type_b) in
    match b.style with
    | Explicit  -> sprintf "(%s)" content
    | Implicit  -> sprintf "{%s}" content
    | Instance  -> sprintf "[%s]" content
  
  let binders_to_string (bs : binder list) : string   =
    String.concat " " (List.map binder_to_string bs)
  
  (* Declaration printing *)
  let rec decl_to_string (d : decl) : string   =
    match d with
    | Import name   ->
        sprintf "import %s" name
    | Variable bs   ->
        sprintf "variable %s" (binders_to_string bs)
    | Definition {  is_noncomputable; name; params; type_v; body } ->
        let prefix      = (if is_noncomputable then "noncomputable " else "") ^ "def " in
        let params_str  = binders_to_string params in
        let type_str    = match type_v with
                            | Some ty   -> sprintf " : %s" (expr_to_string ty)
                            | None      -> ""
        in
        sprintf "%s%s %s%s := %s" prefix name params_str type_str (expr_to_string body)
    | Lemma { name; params; type_b; body }      ->
        sprintf "lemma %s %s :\n %s := %s" name (binders_to_string params) (expr_to_string type_b)
        (expr_to_string body)
    | Notation { is_local; symbol; definition } ->
        let local_str = if is_local then "local " else "" in
        sprintf "%snotation \"%s\" => %s" local_str symbol (expr_to_string definition)
    | DocComment (comment, decl)                ->
        sprintf "/-- %s -/\n%s" comment (decl_to_string decl)
  
(* Main function to print the file *)
let lean_ast_to_lean_file (file : lean_file) : string =
    let header_str =
      match file.header with
        | Some h    -> sprintf "/- %s -/\n\n" h
        | None      -> ""
    in
    let imports_str   = String.concat "\n"    (List.map decl_to_string file.imports)      in
    let decls_str     = String.concat "\n\n"  (List.map decl_to_string file.declarations)  in
  
    header_str ^ imports_str ^ "\n\n" ^ decls_str
