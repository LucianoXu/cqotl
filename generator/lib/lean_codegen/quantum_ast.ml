(************************************************************************************************)
(* This file holds the specific intermediate AST for giving concise semantics to generate LEAN4 *)
(************************************************************************************************)

type qType =
  | Q_Bool
  | Q_Int               
  | Q_KField
  | Q_VectorType
  | Q_OperatorType    (* Always Qbit to Qbit *)
  | Q_TensorType      of qType * qType
  | Q_Arrow           of qType * qType

type quantumTerm =
  | Q_Ket0
  | Q_Ket1
  | Q_Bra0
  | Q_Bra1
  | Q_ZeroOperator
  | Q_IdOperator
  | Q_QuantumVar      of string
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

type proposition =
  | Prop_True                                         (* True *)
  | Prop_False                                        (* False *)  
  | Prop_EqualsQ    of quantumTerm * quantumTerm      (* A = B *)
  | Prop_And        of proposition * proposition      (* P ∧ Q *)
  | Prop_Not        of proposition                    (* ¬P *)
  | Prop_Implies    of proposition * proposition      (* P ⇒ Q *)
  | Prop_Or         of proposition * proposition      (* P ∨ Q *)
  | Prop_Exists     of string * proposition           (* ∃x P(x) *)
  | Prop_Forall     of string * qType * proposition   (* ∀x P(x) *)
  | Prop_Lowner     of quantumTerm * quantumTerm      (* A ≤ B *)
  | Prop_DensityOp  of quantumTerm                    (* isDensityOperator A *)
  | Prop_UnitaryOp  of quantumTerm                    (* isUnitaryOperator A *)
  | Prop_IsSubspace of quantumTerm * quantumTerm      (* isSubspace A B *)
