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

/-- Positive semidefinite operators. -/
def LinearMap.isPositive (T : E →ₗ[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ RCLike.re (inner (T x) x : 𝕜)

/-- Partial density operators. -/
noncomputable def LinearMap.isPartialDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ LinearMap.trace 𝕜 E T ≤ 1

/-- Density operators. -/
noncomputable def LinearMap.isDensityOperator (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ LinearMap.trace 𝕜 E T = 1

/-- Quantum predicate. -/
def LinearMap.isEffect (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ (LinearMap.id - T).isPositive

/-- Unitary operators. In Mathlib we have `IsUnit T`, but it is a different thing. -/
def LinearMap.isUnitary (T : E →ₗ[𝕜] E) : Prop :=
  T * T.adjoint = LinearMap.id

/-- Projection operator -/
def LinearMap.isProjection (T : E →ₗ[𝕜] E) : Prop :=
  T.isPositive ∧ T * T = T

/-- Löwner order between operators. -/
def LinearMap.LoewnerOrder (T N : E →ₗ[𝕜] E) : Prop :=
  (T - N).isPositive

/-- Pure state operators. -/
noncomputable def LinearMap.isPureState (T : E →ₗ[𝕜] E) : Prop :=
  T.isDensityOperator ∧ T.rank = 1
