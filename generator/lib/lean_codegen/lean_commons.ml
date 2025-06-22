(****************************************************************************)
(* The file to hold the commons representation Quantum to LEAN4 AST         *)
(* These commons representations are utilized during LEAN4 code generation  *)
(****************************************************************************)

open Lean_ast
open Printf
open Lean_printer

let commonsImport         = Import "LeanVeri.Commons"
let propositionImport     = Import "LeanVeri.LinearMapPropositions"
let projectionImport      = Import "LeanVeri.ProjectionSubmodule"

let v x                   = Var x
let app f x               = App (f, x)
let app_curried f args    = List.fold_left app f args
let forall name ty body   = Forall (name, ty, body)
let linearMapType         = GenericRepr "𝕜² →ₗ[𝕜] 𝕜²"
let vectorType            = GenericRepr "𝕜²"
let rcLikeType            = GenericRepr "𝕜"
let intType               = GenericRepr "ℤ"
let boolType              = GenericRepr "Bool"
let arrowType t1 t2       = GenericRepr (sprintf "(%s → %s)" (expr_to_string t1) (expr_to_string t2))
let tensorType t1 t2      = GenericRepr (sprintf "(%s ⊗ₗ %s)" (expr_to_string t1) (expr_to_string t2))
let lessThan_v            = v "lt" 
let ket0_v                = v "ket0"
let ket1_v                = v "ket1"
let ketbra0_v             = v "ketbra0"
let ketbra1_v             = v "ketbra1"
let ket0bra0_v            = v "ket0bra0"
let ketPlus_v             = v "ketPlus"
let ketPbraP_v            = v "ketPbraP"
let hadamard_v            = v "H"
let ket1bra1_v            = v "ket1bra1"
let ketbra_v x            = v (sprintf "ketbra%s" x)
let adjoint_v x           = v (sprintf "%s.adjoint" x)
let loewnerOrder e1 e2    = (app (app (v "LinearMap.LoewnerOrder") e1) e2)
let outerProduct e1 e2    = (app (app (app (v "outerProduct") (v "𝕜")) e1) e2)
let applyH e              = (app hadamard_v e) 
let trace e1              = (app (app (app (v "LinearMap.trace") rcLikeType) vectorType) e1)

let supp operator         = app (v "LinearMap.toSubmodule") operator
let image operator        = app (v "LinearMap.toSubmodule") operator
let isDensityOperator op  = app (v "LinearMap.isDensityOperator") op
let annotation e1 e2      = Annotation (e1, e2)
(* let subspace p1 p2        = BinOp ("≤", supp p1, image p2) *)

let mult e1 e2            = BinOp ("*", e1, e2)
let add e1 e2             = BinOp ("+", e1, e2)
let equal e1 e2           = BinOp ("=", e1, e2)
let imply e1 e2           = BinOp ("→", e1, e2)
let lean_and e1 e2        = BinOp ("∧", e1, e2)
let lean_or e1 e2         = BinOp ("∨", e1, e2)
let lean_not e            = UnOp  ("¬", e)

let declarationRCLikeK    = Variable [
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
let functionDef name' typ'= Definition {
                            is_noncomputable = false; name = name'; params = []; type_v = Some typ'; body = Sorry
                          }
let notationDefEuclidean  = Notation {
                            is_local          = true;
                            symbol            = "𝕜²";
                            definition        = app (app (v "EuclideanSpace") rcLikeType) (app (v "Fin") (LitInt 2))
                          }
let hadamardDefinition    = linearMapDefinition "H"         true
let ketPlusDefinition     = vectorDefinition    "ketPlus"   true
let ketMinusDefinition    = vectorDefinition    "ketMinus"  true
let ket0Bra0Definition    = linearMapDefinition "ket0bra0"  false
let ket1Bra1Definition    = linearMapDefinition "ket1bra1"  false
let ketPBraPDefinition    = linearMapDefinition "ketPbraP"  false
let ketMBraMDefinition    = linearMapDefinition "ketMBraM"  false
let hypothesis name' typ  = { name = name'; type_b = typ; style = Explicit}
let densityOperator id    = hypothesis (sprintf "ρ%d" id) linearMapType
let subspace op1 op2      = BinOp ("≤", supp op1, supp op2)
let obligation typ params'= Lemma {
                              name   = sprintf "obligation";
                              params = params';
                              type_b = typ;
                              body   = Sorry;}