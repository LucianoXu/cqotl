/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.TensorProduct.Basic
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
  T ∘ₗ T.adjoint = id

/-- Projection operator -/
def isProjection (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ T ∘ₗ T = T

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

end InnerProductSpace

namespace LinearMap
omit [CompleteSpace E] [FiniteDimensional 𝕜 E]

open scoped TensorProduct

lemma zero_comp' (T : E →ₗ[𝕜] E) : (0 : E →ₗ[𝕜] E) ∘ₗ T = 0 := zero_comp T

lemma comp_zero' (T : E →ₗ[𝕜] E) : T ∘ₗ (0 : E →ₗ[𝕜] E) = 0 := MulZeroClass.mul_zero T

lemma one_comp (T : E →ₗ[𝕜] E) : 1 ∘ₗ T = T := rfl

lemma comp_one (T : E →ₗ[𝕜] E) : T ∘ₗ 1 = T := rfl

lemma scalar_mul_assoc (T : E →ₗ[𝕜] E) (a b : 𝕜) : (a • b) • T = a • (b • T) := IsScalarTower.smul_assoc a b T

lemma zero_add (T : E →ₗ[𝕜] E) : 0 + T = T := AddZeroClass.zero_add T

lemma add_zero (T : E →ₗ[𝕜] E) : T + 0 = T := AddZeroClass.add_zero T

lemma add_conmm (T N : E →ₗ[𝕜] E) : T + N = N + T := AddCommGroup.add_comm T N

lemma add_assoc (T N M : E →ₗ[𝕜] E) : T + (N + M) = (T + N) + M := (_root_.add_assoc T N M).symm

lemma zero_tmul (T : E →ₗ[𝕜] E) : (0 : E) ⊗ₜ[𝕜] T = 0 := TensorProduct.zero_tmul E T

lemma tmul_zero (T : E →ₗ[𝕜] E) : T ⊗ₜ[𝕜] (0 : E) = 0 := TensorProduct.tmul_zero E T

-- lemma tmul_assoc (T N M : E →ₗ[𝕜] E) : (T ⊗ₜ[𝕜] N) ⊗ₜ[𝕜] M = T ⊗ₜ[𝕜] (N ⊗ₜ[𝕜] M) := sorry

lemma tmul_add (T T0 T1 : E →ₗ[𝕜]E) : T ⊗ₜ[𝕜] (T0 + T1) = T ⊗ₜ[𝕜] T0 + T ⊗ₜ[𝕜] T1 := TensorProduct.tmul_add T T0 T1

lemma tmul_add' (T T0 T1 : E →ₗ[𝕜]E) (m : 𝕜) : T ⊗ₜ[𝕜] (m • T0 + T1) = m • (T ⊗ₜ[𝕜] T0) + (T  ⊗ₜ[𝕜] T1) := by
  rw [TensorProduct.tmul_add T (m • T0) T1]
  simp

lemma add_tmul (T T0 T1 : E →ₗ[𝕜]E) : (T + T0) ⊗ₜ[𝕜] T1 = T ⊗ₜ[𝕜] T1 + T0 ⊗ₜ[𝕜] T1 := TensorProduct.add_tmul T T0 T1

lemma add_tmul' (T T0 T1 : E →ₗ[𝕜]E) (m : 𝕜) : (m • T + T0) ⊗ₜ[𝕜] T1 = m • (T ⊗ₜ[𝕜] T1) + (T0 ⊗ₜ[𝕜] T1) := by
  rw [TensorProduct.add_tmul (m • T) T0 T1]
  rfl

lemma adjoint_zero (T : E →ₗ[𝕜]E) : InnerProductSpace.adjoint (0 : E) (T (0 : E)) = (0 : 𝕜) := by
  simp

lemma mul_assoc (T N M : E →ₗ[𝕜]E) : T ∘ₗ (N ∘ₗ M) = (T ∘ₗ N) ∘ₗ M := rfl

lemma adjoint_mul_assoc [FiniteDimensional 𝕜 E] (T N0 N1 : E →ₗ[𝕜] E) :
    N1.adjoint ∘ₗ (N0.adjoint ∘ₗ T ∘ₗ N0) ∘ₗ N1 = (N0 ∘ₗ N1).adjoint ∘ₗ T ∘ₗ (N0 ∘ₗ N1) := by
  simp [mul_assoc, adjoint_comp]

lemma adjoint_dist_adjoint [FiniteDimensional 𝕜 E] (T0 T1 N : E →ₗ[𝕜] E) (m : 𝕜) :
    N.adjoint ∘ₗ (m • T0 + T1) ∘ₗ N = m • (N.adjoint ∘ₗ T0 ∘ₗ N) + (N.adjoint ∘ₗ T1 ∘ₗ N) := by
  rw [add_comp, comp_add, ← comp_assoc, comp_smul, smul_comp, comp_assoc]

end LinearMap

