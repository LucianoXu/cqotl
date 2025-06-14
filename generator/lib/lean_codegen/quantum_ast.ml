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
  | ETrace            of expr
  [@@deriving show]

  type quantumTerm    =
  | Q_Ket0
  | Q_Ket1
  | Q_Bra0
  | Q_Bra1
  | Q_ZeroOperator
  | Q_IdOperator
  | Q_Var             of string
  | Q_ScalarMult      of int * quantumTerm
  | Q_Adjoint         of quantumTerm
  | Q_Apply           of quantumTerm * quantumTerm  (* (A B) *)
  | Q_Add             of quantumTerm * quantumTerm  (* A + B *)
  | Q_Sub             of quantumTerm * quantumTerm  (* A - B *)
  | Q_Mul             of quantumTerm * quantumTerm  (* A * B *)
  | Q_Div             of quantumTerm * quantumTerm  (* A / B *)
  | Q_InnerProduct    of quantumTerm * quantumTerm  (* <A|B> *)
  | Q_Tensor          of quantumTerm * quantumTerm  (* A ⊗ B *)
  | Q_OuterProduct    of quantumTerm * quantumTerm  (* A ⊗ B† *)
  | Q_Trace           of quantumTerm                (* Tr A *)
  | Q_PartialTrace    of int * quantumTerm          (* Tr_i A *)
  | Q_DensityOperator of quantumTerm                (* ρ *)
  [@@deriving show]

type classicalTerm  =
| C_Bool           of bool
| C_Int            of int
| C_ClassicalVar   of string
| C_ScalarMult     of int * classicalTerm
| C_Apply          of classicalTerm * classicalTerm  (* (a b) *)
| C_Add            of classicalTerm * classicalTerm
| C_Sub            of classicalTerm * classicalTerm
| C_Mul            of classicalTerm * classicalTerm
| C_Div            of classicalTerm * classicalTerm
| C_Equals         of classicalTerm * classicalTerm
[@@deriving show]


type proposition    =
  | Prop_True                                         (* True *)
  | Prop_False                                        (* False *)  
  | Prop_EqualsC    of classicalTerm * classicalTerm  (* a = b *)
  | Prop_EqualsQ    of quantumTerm * quantumTerm      (* A = B *)
  | Prop_EqualsP    of proposition * proposition      (* P = Q *)
  | Prop_AndC       of classicalTerm * classicalTerm  (* a ∧ b *) 
  | Prop_AndQ       of quantumTerm * quantumTerm      (* A ∧ B *)
  | Prop_AndP       of proposition * quantumTerm      (* P ∧ Q *)
  | Prop_Not        of proposition                    (* ¬P *)
  | Prop_Implies    of proposition * proposition      (* P ⇒ Q *)
  | Prop_Or         of proposition * proposition      (* P ∨ Q *)
  | Prop_Exists     of string * proposition           (* ∃x P(x) *)
  | Prop_Forall     of string * qType * proposition   (* ∀x P(x) *)
  | Prop_Lowner     of quantumTerm * quantumTerm      (* A ≤ B *)
  | Prop_DensityOp  of quantumTerm                    (* isDensityOperator A *)
  | Prop_UnitaryOp  of quantumTerm                    (* isUnitaryOperator A *)
  | Prop_IsSubspace of quantumTerm * quantumTerm      (* isSubspace A B *)
  [@@deriving show]

(* I need an AST for Assumption and Definition *)
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
