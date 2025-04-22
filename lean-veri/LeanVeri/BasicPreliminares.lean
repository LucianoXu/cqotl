/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Trace
open scoped ComplexOrder

/-!
# Some basic definitions about quantum computing

This file contains some basic definitions and lemmas about quantum computing that are not already in Mathlib.

Some of this may be later added to Mathlib.
-/

variable {𝕜 E : Type*} [RCLike 𝕜]

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]

namespace LinearMap

/-- Positive semidefinite operators. -/
def isPositive (T : E →ₗ[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ RCLike.re (inner (T x) x : 𝕜)

/-- Partial density operators. -/
noncomputable def isPartialDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ trace 𝕜 E T ≤ 1

/-- Density operators. -/
noncomputable def isDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ trace 𝕜 E T = 1

/-- Quantum predicate. -/
def isEffect (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ (id - T).isPositive

/-- Unitary operators. In Mathlib we have `IsUnit T`, but it is a different thing. -/
def isUnitary (T : E →ₗ[𝕜] E) : Prop :=
  T * T.adjoint = id

/-- Projection operator -/
def isProjection (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ T * T = T

/-- Löwner order between operators. -/
def LoewnerOrder (T N : E →ₗ[𝕜] E) : Prop :=
  (T - N).isPositive

/-- Pure state operators. -/
noncomputable def isPureState (T : E →ₗ[𝕜] E) : Prop :=
  T.isDensityOperator ∧ T.rank = 1

end LinearMap

namespace InnerProductSpace

/-- The adjoint of a vector is a linear map that takes a vector and returns the inner product with the given vector. -/
def adjoint (φ : E) : E →ₗ[𝕜] 𝕜 where
  toFun := fun χ => inner φ χ
  map_add' := inner_add_right φ
  map_smul' := by
    intro m χ
    exact inner_smul_right_eq_smul φ χ m

/-- The outer product of two vectors -/
def outerProduct (φ : E) (ψ : E) : E →ₗ[𝕜] E where
  toFun := fun χ => (inner ψ χ : 𝕜) • φ
  map_add' := by
    intro χ η
    rw [← Module.add_smul]
    rw [inner_add_right ψ χ η]
  map_smul' := by
    intro m χ
    rw [RingHom.id_apply]
    rw [inner_smul_right_eq_smul ψ χ m]
    exact IsScalarTower.smul_assoc m (inner ψ χ) φ

/-- The bra of a vector is a linear map. -/
notation:max "⟨" φ "|" => adjoint φ

/-- The ket of a vector is it self. -/
notation:max "|" φ "⟩" => φ

/-- The inner product of two vectors. -/
notation:max "⟨" φ "|" ψ "⟩" => inner φ ψ

/-- The outer product of two vectors. -/
notation:max "|" φ "⟩⟨" ψ "|" => outerProduct φ ψ

end InnerProductSpace
