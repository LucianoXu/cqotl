(************************************************************************************************)
(* This file holds the specific intermediate AST for giving concise semantics to generate LEAN4 *)
(************************************************************************************************)

type qType        =
  | TyBool
  | TyInt               
  | TyKField
  | TyVectorType
  | TyOperatorType    (* Always Qbit to Qbit *)
  | TyTensorType      of qType * qType
  | TyArrow           of qType * qType
  | TyProjectorType
  | TyDensityOperatorType
  | TyProp
  [@@deriving show]

type expr =
  | EZeroOp
  | EIdentOp
  | EBool             of bool
  | EInt              of int
  | EVar              of string
  | EKet              of expr
  | EBra              of expr
  | EScalarMult       of int * expr
  | EAdjoint          of expr
  | E_Eq              of expr * expr
  | E_Eqeq            of expr * expr
  | EImply            of expr * expr
  | EAnd              of expr * expr
  | EOr               of expr * expr
  | EApply            of expr * expr  
  | EForall           of string * expr * expr
  | EType             of qType
  | ENot              of expr
  | ESubspace         of expr * expr
  | ELownerOrder      of expr * expr
  | ETrace            of expr
  [@@deriving show]

(* Assumption ~~~> Definition with Sorry *)
(* Definition ~~~> Definition with quantum Term *)
type quantumEnv   =
  | QuantumAssumption of {name: string; t: qType}                 (* ~~~> Def with sorry *)
  | QuantumDefinition of {name: string; t: qType; e: expr}        (* ~~~> Def with concrete specification *)
  [@@deriving show]

type lean_obligation = {
    definitions : quantumEnv list;
    variables   : (string * qType) list;
    goal        : expr;
  }[@@deriving show]
