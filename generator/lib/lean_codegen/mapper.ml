open Quantum_ast
open Lean_ast
(* open Printf *)
open Lean_commons
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
      Result (tensorType t1_lean t2_lean)
  | TyProjectorType       -> Result (linearMapType)
  | TyDensityOperatorType -> Result (linearMapType)
  | _                     -> 
    LeanTranslationError ("Unsupported quantum type in qtype_to_lean_expr: " ^ (show_qType qt))
  (* | TyProp               -> GenericRepr "Prop" *)

(* Function to convert a Intermediate Quantum Expr to a LEAN Expression *)
let rec quantum_expr_to_lean_expr (qe : Quantum_ast.expr) : (Lean_ast.expr, string) lean4Result =
  match qe with
  | EBool false           -> Result (GenericRepr "true") (* Using Int to represent Bool *)
  | EBool true            -> Result (GenericRepr "false") (* Using Int to represent Bool *)
  | EInt n                -> Result (LitInt n)
  | EVar x                -> Result (v x)
  | EScalarMult (n, e)    ->
      quantum_expr_to_lean_expr e >>= fun e_lean ->
      Result (mult (LitInt n) e_lean)
  | EAdjoint _            ->
      LeanTranslationError "Adjoint operation not supported in quantum_expr_to_lean_expr"
  | E_Eq (e1, e2)         ->
      quantum_expr_to_lean_expr e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr e2 >>= fun e2_lean ->
      Result (equal e1_lean e2_lean)
  | E_Eqeq (e1, e2)       ->
      quantum_expr_to_lean_expr e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr e2 >>= fun e2_lean ->
      Result (BinOp ("=", e1_lean, e2_lean))
  | EImply (e1, e2)       ->
      quantum_expr_to_lean_expr e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr e2 >>= fun e2_lean ->
      Result (imply e1_lean e2_lean)
  | EAnd (e1, e2)         ->
      quantum_expr_to_lean_expr e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr e2 >>= fun e2_lean ->
      Result (lean_and e1_lean e2_lean)
  | EOr (e1, e2)          ->
      quantum_expr_to_lean_expr e1 >>= fun e1_lean ->
      quantum_expr_to_lean_expr e2 >>= fun e2_lean ->
      Result (lean_or e1_lean e2_lean)
  | EApply (f, x)         ->
      quantum_expr_to_lean_expr f >>= fun f_lean  ->
      quantum_expr_to_lean_expr x >>= fun x_lean  ->
      Result (app f_lean x_lean)
  | EForall (x, qt, e)    ->
      qtype_to_lean_expr qt       >>= fun qt_lean ->
      quantum_expr_to_lean_expr e >>= fun e_lean  ->
      Result (Lambda (x, qt_lean, e_lean))
  | ENot e               ->
      quantum_expr_to_lean_expr e >>= fun e_lean ->
      Result (lean_not e_lean)

(* let transform_ *)