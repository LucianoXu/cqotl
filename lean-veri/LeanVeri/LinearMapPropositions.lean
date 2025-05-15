/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison, Jam Khan
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Support
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.Filter.Ker

open scoped ComplexOrder
/-!
# Some basic propositions about `LinearMap`

This file contains some basic propositions about `LinearMap` that are not already in Mathlib.
Some of this may be later added to Mathlib.
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]

variable? [HilbertSpace 𝕜 F] => [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [FiniteDimensional 𝕜 F]

namespace LinearMap

/-- Positive semidefinite operators. -/
def isPositiveSemiDefinite (T : E →ₗ[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ RCLike.re (inner 𝕜 (T x) x)

/-- Positive definite operators. -/
def isPositiveDefinite (T : E →ₗ[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 < RCLike.re (inner 𝕜 (T x) x)

/-- Partial density operators. -/
def isPartialDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositiveSemiDefinite ∧ trace 𝕜 E T ≤ 1

/-- Density operators. -/
def isDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositiveSemiDefinite ∧ trace 𝕜 E T = 1

/-- Quantum predicate. -/
def isEffect (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositiveSemiDefinite ∧ (id - T).isPositiveSemiDefinite

/-- Isometry operators. -/
def isIsometry (T : E →ₗ[𝕜] F) : Prop :=
  T.adjoint ∘ₗ T = id

/-- Unitary operators. The same as isometry, but for `E →ₗ[𝕜] E`.
In Mathlib we have `IsUnit T`, but it is a different thing. -/
def isUnitary (T : E →ₗ[𝕜] E) : Prop :=
  T.isIsometry

/-- Projection operator -/
def isProjection (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositiveSemiDefinite ∧ T ∘ₗ T = T

/-- Löwner order between operators. -/
def LoewnerOrder (T N : E →ₗ[𝕜] E) : Prop :=
  (T - N).isPositiveSemiDefinite

/-- Pure state operators. -/
def isPureState (T : E →ₗ[𝕜] E) : Prop :=
  T.isDensityOperator ∧ T.rank = 1

/-- The outer product of two vectors -/
def outerProduct (φ : E) (ψ : E) : E →ₗ[𝕜] E where
  toFun := fun χ => (inner 𝕜 ψ χ : 𝕜) • φ
  map_add' := by
    intro χ η
    rw [← Module.add_smul]
    rw [inner_add_right ψ χ η]
  map_smul' := by
    intro m χ
    rw [RingHom.id_apply]
    rw [inner_smul_right_eq_smul ψ χ m]
    exact IsScalarTower.smul_assoc m (inner 𝕜 ψ χ) φ

end LinearMap
