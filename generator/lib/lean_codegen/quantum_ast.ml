(************************************************************************************)
(* This file holds the mechanism to generate LEAN4_AST from the CQOTL Prover syntax *)
(* To be implemented                                                                *)
(************************************************************************************)

type binOp  =
  | Add
  | Sub
  | Mult
  | Outer
  | Tensor
  | KetBra
 
type unOp =
  | Adjoint
  | Supp
  | Image
  | Trace
  | PartialTrace1
  | PartialTrace2

type quantumTerm =
  | Ket0
  | Ket1
  | IdOperator
  | ZeroOperator
  | UnaryOp       of unOp  * quantumTerm
  | BinaryOp      of binOp * quantumTerm * quantumTerm
