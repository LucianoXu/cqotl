open Quantum_ast
open Lean_ast
open Lean_commons
(* open Printf *)
open Ast

(* Function to convert a Quantum Type to a LEAN Type *)
let rec qtype_to_lean_expr (qt : qType) : (Lean_ast.expr, string) lean4Result =
  match qt with
  | TyBool                -> Result (boolType)
  | TyInt                 -> Result (intType)
  | TyKField              -> Result (rcLikeType)
  | TyVectorType          -> Result (vectorType)
  | TyOperatorType        -> Result (linearMapType)
  | TyTensorType (t1, t2) ->
      qtype_to_lean_expr t1 >>= fun t1_lean ->
      qtype_to_lean_expr t2 >>= fun t2_lean ->
      Result (tensorType t1_lean t2_lean)
  | TyArrow (t1, t2)      ->
      qtype_to_lean_expr t1 >>= fun t1_lean ->
      qtype_to_lean_expr t2 >>= fun t2_lean ->
      Result (arrowType t1_lean t2_lean)
  | TyProjectorType       -> Result (linearMapType)
  | TyDensityOperatorType -> Result (linearMapType)
  | _                     -> 
    LeanTranslationError ("Unsupported quantum type in qtype_to_lean_expr: " ^ (show_qType qt))
  (* | TyProp               -> GenericRepr "Prop" *)

module StringMap = Map.Make(String)

(* Helper function to extract typing information from obligation *)
let extract_ty_context (obl: lean_obligation) : (string * qType) list =
  let defs_as_bindings =
    List.map (fun env_item ->
      match env_item with
      | QuantumAssumption {name; t} -> (name, t)
      | QuantumDefinition {name; t; e=_} -> (name, t)
    ) obl.definitions
  in  let all_bindings = defs_as_bindings @ obl.variables 
  in  let unique_map =
        List.fold_left
          (fun acc_map (name, qtype) -> StringMap.add name qtype acc_map)
          StringMap.empty
          all_bindings
  in  StringMap.bindings unique_map

(* Helper function to check an operator type *)
let is_operator_type (qt: qType) : bool =
  match qt with
  | TyOperatorType | TyProjectorType | TyDensityOperatorType  -> true
  | _                                                         -> false

(* Helper function to check*)
let rec infer_qtype (ty_ctx : (string * qType) list) (qe : Quantum_ast.expr) : (qType, string) lean4Result =
  match qe with
  | EVar name   ->
      (match List.assoc_opt name ty_ctx with
      | Some qt     -> Result qt
      | None        -> LeanTranslationError ("Type of variable '" ^ name ^ "' not found in context."))
  | EAdjoint e  ->
      infer_qtype ty_ctx e
  | _  ->
    Result (TyBool) (* Default type for unsupported expressions, can be adjusted *)

(* Function to convert a Intermediate Quantum Expr to a LEAN Expression *)
let rec quantum_expr_to_lean_expr (ty_ctx : (string * qType) list) (qe : Quantum_ast.expr) : (Lean_ast.expr, string) lean4Result =
  match qe with
  | EBool false           -> Result (GenericRepr "false")  (* Using Int to represent Bool *)
  | EBool true            -> Result (GenericRepr "true") (* Using Int to represent Bool *)
  | EKet (EBool false)    -> Result (ket0_v)
  | EKet (EBool true)     -> Result (ket1_v)
  | EApply (EKet (EBool false), EBra (EBool false))
                          -> Result (ketbra0_v)
  | EApply (EVar x, EAdjoint (EVar y)) when x = y ->
      Result (annotation (outerProduct (v x) (v y)) linearMapType)
  | EAdjoint (EVar x)                             ->
      Result (adjoint_v x)
  | EApply (EKet (EBool true), EBra (EBool true))
                          -> Result (ketbra1_v)
  | EInt n                -> Result (LitInt n)
  | EVar x                -> Result (v x)
  | EScalarMult (n, e)    ->
      quantum_expr_to_lean_expr ty_ctx e >>= fun e_lean ->
      Result (mult (LitInt n) e_lean)
  | EAdjoint _            ->
      LeanTranslationError "Adjoint operation not supported in quantum_expr_to_lean_expr"
  | E_Eq (e1, e2)         ->
      quantum_expr_to_lean_expr ty_ctx e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr ty_ctx e2 >>= fun e2_lean ->
      Result (equal e1_lean e2_lean)
  | E_Eqeq (e1, e2)       ->
      quantum_expr_to_lean_expr ty_ctx e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr ty_ctx e2 >>= fun e2_lean ->
      Result (BinOp ("=", e1_lean, e2_lean))
  | EImply (e1, e2)       ->
      quantum_expr_to_lean_expr ty_ctx e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr ty_ctx e2 >>= fun e2_lean ->
      Result (imply e1_lean e2_lean)
  | EAnd (e1, e2)         ->
      quantum_expr_to_lean_expr ty_ctx e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr ty_ctx e2 >>= fun e2_lean ->
      Result (lean_and e1_lean e2_lean)
  | EOr (e1, e2)          ->
      quantum_expr_to_lean_expr ty_ctx e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr ty_ctx e2 >>= fun e2_lean ->
      Result (lean_or e1_lean e2_lean)
  | EApply (f, x)         ->
      infer_qtype ty_ctx f >>= fun f_qtype ->
      infer_qtype ty_ctx x >>= fun x_qtype ->
      quantum_expr_to_lean_expr ty_ctx f >>= fun f_lean ->
      quantum_expr_to_lean_expr ty_ctx x >>= fun x_lean ->
      if is_operator_type f_qtype || is_operator_type x_qtype then
        Result (mult f_lean x_lean)
      else
        Result (app f_lean x_lean)
  | EForall (x, EType qt, e)           ->
      quantum_expr_to_lean_expr ty_ctx (EType qt)  >>= fun qt_lean      ->
      let new_ty_ctx = (x, qt) :: ty_ctx                  in
        quantum_expr_to_lean_expr new_ty_ctx e   >>= fun e_lean ->
        Result (Forall (x, qt_lean, e_lean))
  | EForall (x, qt, e)    ->
      quantum_expr_to_lean_expr ty_ctx qt  >>= fun qt_lean ->
      quantum_expr_to_lean_expr ty_ctx e   >>= fun e_lean  ->
      Result (Forall (x, qt_lean, e_lean))
  | ENot e                ->
      quantum_expr_to_lean_expr ty_ctx e >>= fun e_lean ->
      Result (lean_not e_lean)
  | EType qty             ->
      qtype_to_lean_expr qty
  | ELownerOrder (p1, p2) ->
      quantum_expr_to_lean_expr ty_ctx p1 >>= fun p1_lean ->
      quantum_expr_to_lean_expr ty_ctx p2 >>= fun p2_lean ->
      Result (loewnerOrder p1_lean p2_lean)
  | ESubspace (p1, p2)    ->
      quantum_expr_to_lean_expr ty_ctx p1 >>= fun p1_lean ->
      quantum_expr_to_lean_expr ty_ctx p2 >>= fun p2_lean ->
      Result (BinOp ("≤", supp p1_lean, image p2_lean))
  | EZeroOp               ->
      Result (v "0")
  | ETrace qt              ->
      quantum_expr_to_lean_expr ty_ctx qt >>= fun qt_lean ->
      Result (trace qt_lean)
  | e                     ->
      LeanTranslationError ("Expr to LEAN4 Translation not supported yet: " ^ (Quantum_ast.show_expr e))

(* Helper function to map over a list and collect results monadically *)
let map_m (f : 'a -> ('b, 'e) lean4Result) (lst : 'a list) : ('b list, 'e) lean4Result =
  let rec aux acc l =
    match l with
    | [] -> Result (List.rev acc)
    | x :: xs ->
        f x >>= fun y ->
        aux (y :: acc) xs
  in
  aux [] lst

let transform_obligation_to_lean_file (obl_name : string) (obl : Quantum_ast.lean_obligation) : (lean_file, string) lean4Result =
  let lean_header = Some (Printf.sprintf "LEAN4 FILE AUTO GENERATED BY CQOTL PROVER FOR OBLIGATION: %s" obl_name) in
  let imports = [
    commonsImport;
    propositionImport;
    projectionImport (* Add more as needed *)
  ] in
  let initial_declarations = [
    declarationRCLikeK;
    notationDefEuclidean;
  ] in

  map_m (fun (def : quantumEnv) ->
    match def with
    | QuantumAssumption {name; t} ->
        qtype_to_lean_expr t >>= fun t_lean ->
          Result (Lean_ast.Definition {
            is_noncomputable  = false;
            name              = name;
            params            = [];
            type_v            = Some t_lean;
            body              = Sorry
          } : Lean_ast.decl)
    | QuantumDefinition {name; t; e} ->
        qtype_to_lean_expr t >>= fun t_lean ->
          quantum_expr_to_lean_expr [] e >>= fun body_lean ->
          Result (Lean_ast.Definition {
            is_noncomputable  = false;
            name              = name;
            params            = [];
            type_v            = Some t_lean;
            body              = body_lean
          })
    ) obl.definitions >>= fun definition_declarations ->
      (* Transforming variables now *)
      map_m (fun (name, qt) ->
        qtype_to_lean_expr qt >>= fun lean_type_expr ->
        Result ({
          Lean_ast.name   = name;
          Lean_ast.type_b = lean_type_expr;
          Lean_ast.style  = Lean_ast.Explicit;
        } : Lean_ast.binder)
      ) obl.variables >>= fun lemma_params ->
    (* Transform the goal *)
    quantum_expr_to_lean_expr (extract_ty_context obl) obl.goal >>= fun lean_goal_expr ->

    let main_lemma_decl : Lean_ast.decl = Lean_ast.Lemma {
      name    = obl_name; (* Or a more structured name like "lemma_" ^ obl_name *)
      params  = lemma_params;
      type_b  = lean_goal_expr;
      body    = Lean_ast.Sorry;
    } in
  
    let all_declarations = initial_declarations @ definition_declarations @ [main_lemma_decl] in
  
    Result {
      Lean_ast.header       = lean_header;
      Lean_ast.imports      = imports;
      Lean_ast.declarations = all_declarations;
    }
