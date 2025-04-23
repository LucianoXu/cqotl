/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

variable {n m n' m' R : Type*}
variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [DecidableEq n'] [Fintype n'] [DecidableEq m'] [Fintype m']
variable [CommRing R] [PartialOrder R] [StarRing R]

namespace Matrix

/-- Partial density matrixes. -/
def isPartialDensityOperator (M : Matrix n n R) : Prop :=
  M.PosSemidef ∧ M.trace ≤ 1

/-- Density matrixes. -/
def isDensityOperator (M : Matrix n n R) : Prop :=
  M.PosSemidef ∧ M.trace = 1

/-- Quantum predicate. -/
def isEffect (M : Matrix n n R) : Prop :=
  M.PosSemidef ∧ (1 - M).PosSemidef

/-- Unitary operators. In Mathlib we also have `IsUnit T`, but it is a different thing. -/
def isUnitary (M : Matrix n n R) : Prop :=
  M ∈ Matrix.unitaryGroup n R

/-- Projection matrixes -/
def isProjection (M : Matrix n n R) : Prop :=
  M.PosSemidef ∧ M * M = M

/-- Löwner order between matrixes. In Mathlib we have `ContinuousLinearMap.instLoewnerPartialOrder`, but it is for ContinuousLinearMap, not for `Matrix` -/
def LownerOrder (M N : Matrix n n R) : Prop :=
  (M - N).PosSemidef

/-- Pure state matrixes. -/
def isPureState (M : Matrix n n R) : Prop :=
  M.isDensityOperator ∧ M.rank = 1

def mul_vector (A : Matrix n m R) (v : m → R) : n → R :=
  A *ᵥ v

def mul_matrix {k} [Fintype k] (A : Matrix n m R) (B : Matrix m k R) : Matrix n k R :=
  A * B



/- def adjoint (M : Matrix n n R) : Matrix n n R :=
  Mᴴ -/

end Matrix

def vector_tmul_vector (u : n → R) (v : m → R) : (n × m) → R :=
  fun (i : n × m) => u i.fst * v i.snd

def matrix_tmul_matrix (A : Matrix n m R) (B : Matrix n' m' R) : Matrix (n × m) (n' × m') R :=
  fun (i : n × m) (j : n' × m') => A i.fst i.snd * B j.fst j.snd

