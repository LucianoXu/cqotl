open Quantum_ast
(* open Lean_ast *)
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