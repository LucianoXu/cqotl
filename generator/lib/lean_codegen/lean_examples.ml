(*************************************************************************)
(* The file to hold the Lean_ast representation                          *)
(* All the code to be generated as a LEAN4 file is represented as an AST *)
(* OCAML syntax is converted into LEAN4 AST by the `by_lean` tactic      *)
(* Then, LEAN4 AST is utilized for code generation of the LEAN4 code     *)
(*************************************************************************)
open Lean_ast
open Lean_commons
open Printf

(* Define the representation of LEAN4 as an AST *)
(* type ident = string

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
} *)

(* let commonsImport       = Import "LeanVeri.Commons"
let propositionImport   = Import "LeanVeri.LinearMapPropositions"
let projectionImport    = Import "LeanVeri.ProjectionSubmodule"

let v x                 = Var x
let app f x             = App (f, x)
let app_curried f args  = List.fold_left app f args

let linearMapType       = GenericRepr "𝕜² →ₗ[𝕜] 𝕜²"
let vectorType          = GenericRepr "𝕜²"
let rcLikeType          = GenericRepr "𝕜"

let ket0bra0_v          = v "ket0bra0"
let ketPlus_v           = v "ketPlus"
let ketPbraP_v          = v "ketPbraP"
let hadamard_v          = v "H"
let ket1bra1_v          = v "ket1bra1"

let loewnerOrder e1 e2  = (app (app (v "LinearMap.LoewnerOrder") e1) e2)
let outerProduct e1 e2  = (app (app (app (v "outerProduct") (v "𝕜")) e1) e2)
let applyH e            = (app hadamard_v e) 
let trace e1            = (app (app (app (v "LinearMap.trace") rcLikeType) vectorType) e1)

let supp operator         = app (v "LinearMap.toSubmodule") operator
let image operator        = app (v "LinearMap.toSubmodule") operator
let isDensityOperator op  = app (v "LinearMap.isDensityOperator") op

let mult e1 e2          = BinOp ("*", e1, e2)
let add e1 e2           = BinOp ("+", e1, e2)
let equal e1 e2         = BinOp ("=", e1, e2)

let declarationRCLikeK  = Variable [
                            { name = "𝕜";     type_b = Type; style = Implicit };
                            { name = "_inst"; type_b = app (v "RCLike") rcLikeType; style = Instance }
                          ]
let linearMapDefinition name' computable
                        = Definition {
                            is_noncomputable=computable; name=name'; params = []; type_v = Some linearMapType; body = Sorry 
                          }
let vectorDefinition name' computable
                          = Definition {
                            is_noncomputable=computable; name=name'; params = []; type_v = Some vectorType; body = Sorry 
                          }
let qubitMeasDistr name'  = Definition {
                            is_noncomputable = false; name = name'; params = []; type_v = Some (GenericRepr "Bool → 𝕜"); body = Sorry
                          }
let notationDefEuclidean  = Notation {
                            is_local          = true;
                            symbol            = "𝕜²";
                            definition        = app (app (v "EuclideanSpace") rcLikeType) (app (v "Fin") (LitInt 2))
                          }

let hadamardDefinition    = linearMapDefinition "H" true
let ketPlusDefinition     = vectorDefinition "ketPlus" true
let ketMinusDefinition    = vectorDefinition "ketMinus" true
let ket0Bra0Definition    = linearMapDefinition "ket0bra0" false
let ket1Bra1Definition    = linearMapDefinition "ket1bra1" false
let ketPBraPDefinition    = linearMapDefinition "ketPbraP" false
let ketMBraMDefinition    = linearMapDefinition "ketMBraM" false

let hypothesis name' typ  = { name = name'; type_b = typ; style = Explicit}

let densityOperator id    = hypothesis (sprintf "ρ%d" id) linearMapType

let subspace op1 op2      = BinOp ("≤", supp op1, supp op2)

let obligation id typ params'  
                          = Lemma {
                              name   = sprintf "obligation%d" id;
                              params = params';
                              type_b = typ;
                              body   = Sorry;} *)

let example1 : lean_file = {
  header  = Some "LEAN4 FILE AUTO GENERATED BY CQOTL PROVER FOR PROOF OBLIGATIONS";
  imports = [
    commonsImport;
    propositionImport;
  ];
  declarations = [
    declarationRCLikeK;
    notationDefEuclidean;
    hadamardDefinition;
    ketPlusDefinition;
    ket0Bra0Definition;
    ket1Bra1Definition;
    obligation 1 (loewnerOrder ket0bra0_v (outerProduct (applyH ketPlus_v) (applyH ketPlus_v))) []
  ];
}

let example2 : lean_file = {
  header  = Some "LEAN4 FILE AUTO GENERATED BY CQOTL PROVER FOR PROOF OBLIGATIONS";
  imports = [
    commonsImport;
    propositionImport;
    projectionImport;
  ];
  declarations = [
    declarationRCLikeK;
    notationDefEuclidean;
    qubitMeasDistr "μ";
    ket0Bra0Definition;
    ketPBraPDefinition;
    obligation 1 (equal (trace (mult ket0bra0_v (v "ρ1"))) (app (v "μ") (v "false"))) [densityOperator 1; hypothesis "h1" (isDensityOperator (v "ρ1"));  hypothesis "h2" (subspace (v "ρ1") ketPbraP_v);]
  ]
}

let example3 : lean_file = {
  header  = Some "LEAN4 FILE AUTO GENERATED BY CQOTL PROVER FOR PROOF OBLIGATIONS";
  imports = [
    commonsImport;
    propositionImport;
    projectionImport;
  ];
  declarations = [
    declarationRCLikeK;
    notationDefEuclidean;
    qubitMeasDistr "μ";
    ket1Bra1Definition;
    ketPBraPDefinition;
    obligation 1 (equal (trace (mult ket1bra1_v (v "ρ1"))) (app (v "μ") (v "true"))) [densityOperator 1; hypothesis "h1" (isDensityOperator (v "ρ1"));  hypothesis "h2" (subspace (v "ρ1") ketPbraP_v);]
  ]
}

let examples : (lean_file * string) list = [
  (example1, "Obligation1-1.lean");
  (example2, "Obligation1-2.lean");
  (example3, "Obligation1-3.lean")
]

(*
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

let () =
  let lean_code_string = lean_ast_to_lean_file example3 in
  print_endline lean_code_string

(* --- File Handling Utilities (kept as before, slightly adjusted messages) --- *)
(* Define the path to the config file *)
let config_file = "cqotl_path.config"

(* Define the relative path from the base CQOTL directory to the Lean Examples directory *)
let relative_lean_examples_dir = "lean-veri/LeanVeri/Examples"

(* Function to read the base path from the config file *)
let read_cqotl_base_path config_path =
  try
    let ic = open_in config_path in
    let base_path = input_line ic in
    close_in ic;
    Some base_path
  with
  | Sys_error msg ->
      eprintf "Error: Could not open or read config file '%s' - %s\n" config_path msg;
      None
  | End_of_file ->
      eprintf "Error: Config file '%s' is empty. Please provide the base CQOTL path.\n" config_path;
      None

(* Function to write content to a file *)
let write_content_to_file filepath content =
  try
    let oc = open_out filepath in
    fprintf oc "%s" content; (* Use %s not %s\n because lean_ast_to_lean_file already adds a newline *)
    close_out oc;
    printf "  -> Successfully wrote Lean code to '%s'\n" filepath;
    true
  with
  | Sys_error msg ->
      eprintf "Error: Could not write to file '%s' - %s\n" filepath msg;
      false

(* --- New function to process a single example --- *)
let process_example (file_ast, filename) =
  printf "Processing example: %s\n" filename;

  (* Generate the Lean code string from the AST *)
  let lean_code_string = lean_ast_to_lean_file file_ast in

  (* Get the base path from the config *)
  match read_cqotl_base_path config_file with
  | Some base_path ->
      (* Construct the full path to the target Lean file *)
      (* First, build the full path to the examples directory *)
      let dir_components = String.split_on_char '/' relative_lean_examples_dir in
      let full_examples_dir = List.fold_left Filename.concat base_path dir_components in
      (* Then, add the specific filename *)
      let full_lean_path = Filename.concat full_examples_dir filename in

      (* Write the generated code to the file *)
      let success = write_content_to_file full_lean_path lean_code_string in
      if not success then
        eprintf "Failed to process example '%s' due to file writing error.\n" filename;
      () (* Return unit *)
  | None ->
      (* Config file reading failed (error message already printed) *)
      eprintf "Skipping example '%s' due to config file error.\n" filename;
      () (* Return unit *)

(* --- Main execution block --- *)
let () =
  printf "Starting Lean file generation from OCaml AST...\n";

  (* Check if the config file exists before starting *)
  if not (Sys.file_exists config_file) then (
    eprintf "Error: Config file '%s' not found. Please create it with the base path of your CQOTL project.\n" config_file;
    exit 1 (* Exit the program if config is missing *)
  );

  (* Iterate through the list of examples and process each one *)
  List.iter process_example examples;

  printf "Finished Lean file generation.\n";
*)