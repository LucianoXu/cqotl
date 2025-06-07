(************************************************************************************)
(* This file holds the mechanism to generate LEAN4_AST from the CQOTL Prover syntax *)
(* To be implemented                                                                *)
(************************************************************************************)

type quantumBinOp =
  | Q_Add           (* A + B *)
  | Q_Sub           (* A - B *)
  | Q_Mult          (* A * B *)
  | Q_Tensor        (* A ⊗ B *)
  | Q_Outer         (*|u⟩⟨v| *)

type quantumUnOp  =
  | Q_Adjoint       (* A†      *)
  | Q_Supp          (* supp(A) *)
  | Q_Image         (* im(A)   *)
  | Q_Trace         (* tr(A)   *)
  | Q_PartialTrace1 (* tr1(A)  *)
  | Q_PartialTrace2 (* tr2(A)  *)

type scalarBinOp  =
  | S_Add
  | S_Sub
  | S_Mult
  | S_Div
  | S_Pow

type classicalBinOp =
  | C_Add
  | C_Sub
  | C_Mult
  | C_Div
  | C_Pow
  | C_And
  | C_Or

type classicalUnOp  =
  | C_Neg
  | C_Not

type comparisonOp   =
  | Cmp_Eq    (* == *)
  | Cmp_Neq   (* != *)
  | Cmp_Lt    (* <  *)
  | Cmp_Le    (* <= *)
  | Cmp_Gt    (* >  *)
  | Cmp_Ge    (* >= *)

type termType =
  | T_Complex         (* Complex numbers *)
  | T_Real            (* Real numbers *)
  | T_Int             (* Integers *)
  | T_Bool
  | T_String
  | T_QuantumState    of int list (* List of dimensions, e.g., [2] for 1 qubit, [2; 2] for 2 qubits *)
  | T_QuantumOperator of int list (* Total dimension if square, e.g. [2;2] for 4x4 op *)

type classicalTerm  =
  | C_bool        of bool
  | C_Int         of int
  | C_Real        of float
  | C_String      of string
  | C_Var         of string
  | C_BinaryOp    of classicalBinOp * classicalTerm * classicalTerm
  | C_UnaryOp     of classicalUnOp * classicalTerm
  | C_Comparison  of comparisonOp * classicalTerm * classicalTerm
  | C_Trace       of quantumTerm 
  | C_MeasOutcome of quantumTerm * quantumTerm
  | C_ExpectVal   of quantumTerm * quantumTerm

and quantumTerm =
  | Q_Ket0
  | Q_Ket1
  | Q_KetP
  | Q_KetM
  | Q_Bra0
  | Q_Bra1
  | Q_BraP
  | Q_BraM
  | Q_IdOperator
  | Q_ZeroOperator
  | Q_Hadamard
  | Q_PauliX
  | Q_PauliZ
  | Q_PauliY
  | Q_QuantumVar  of string
  | Q_ScalarMult  of classicalTerm * quantumTerm
  | Q_Apply       of quantumTerm * quantumTerm
  | UnaryOp       of quantumUnOp  * quantumTerm
  | BinaryOp      of quantumBinOp * quantumTerm * quantumTerm

type proposition =
  | Prop_True
  | Prop_False
  | Prop_EqualsQ          of quantumTerm * quantumTerm      (* A  = B *)
  | Prop_EqualsC          of classicalTerm * classicalTerm  (* c1 = c2 *)
  | Prop_Comparison       of comparisonOp * classicalTerm * classicalTerm
  | Prop_IsUnitary        of quantumTerm
  | Prop_IsHermitian      of quantumTerm
  | Prop_IsDensityMatrix  of quantumTerm
  | Prop_IsNormalized     of quantumTerm
  | Prop_And              of proposition * proposition
  | Prop_Or               of proposition * proposition
  | Prop_Not              of proposition
  | Prop_Implies          of proposition * proposition
  | Prop_Iff              of proposition * proposition
  | Prop_Forall           of string * termType * proposition
  | Prop_Exists           of string * termType * proposition
