/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison, Jam Khan
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace
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

omit [CompleteSpace E] in
lemma isPositiveSemiDefinite.IsSymmetric (T : E →ₗ[𝕜] E) (hT : T.isPositiveSemiDefinite) : T.IsSymmetric :=
  (isSymmetric_iff_isSelfAdjoint T).mpr hT.left

omit [CompleteSpace E] in
lemma isPositiveSemiDefinite_add_of_isPositiveSemiDefinite {T S : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite)
    (hS : S.isPositiveSemiDefinite) : (T + S).isPositiveSemiDefinite := by
  apply And.intro
  · unfold IsSelfAdjoint
    rw [star_add]
    rw [hT.left, hS.left]
  · intro x
    rw [add_apply]
    rw [inner_add_left]
    rw [AddMonoidHom.map_add]
    exact Left.add_nonneg (hT.right x) (hS.right x)

omit [CompleteSpace E] in
lemma isPositiveSemiDefinite.nonneg_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite)
    (i : Fin (Module.finrank 𝕜 E)) : 0 ≤ hT.IsSymmetric.eigenvalues rfl i := by
  have h := hT.right (hT.IsSymmetric.eigenvectorBasis rfl i)
  rw [hT.IsSymmetric.apply_eigenvectorBasis] at h
  rw [inner_smul_real_left] at h
  rw [RCLike.smul_re] at h
  rw [inner_self_eq_norm_sq] at h
  rw [OrthonormalBasis.norm_eq_one] at h
  simp only [one_pow, mul_one] at h
  exact h

lemma aux0 (n : ℕ) (f : Fin n → Fin n → ℝ) :
    ∑i ∈ ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2), f i.1 i.2 =
    ∑i, f i i := by
  let diag := (@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2
  rw [← Lean.Grind.CommRing.add_zero (∑i ∈ ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2), f i.1 i.2)]
  rw [← show ∑i ∈ diagᶜ, (0 : ℝ) = 0 by exact Finset.sum_const_zero]
  have diagc : diagᶜ = ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ ¬i.1 = i.2) := by
    unfold diag
    simp
  rw [diagc]
  rw [← Finset.sum_ite]
  rw [Fintype.sum_prod_type]
  simp

omit [CompleteSpace E] in
lemma isPositiveSemiDefinite.re_inner_app_eq_zero_iff_app_eq_zero {T : E →ₗ[𝕜]E} (hT : T.isPositiveSemiDefinite) (x : E) :
    RCLike.re (inner 𝕜 (T x) x) = 0 ↔ T x = 0 := by
  have hTsymm : T.IsSymmetric := (isSymmetric_iff_isSelfAdjoint T).mpr hT.left
  let n : ℕ := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  let base : OrthonormalBasis (Fin n) 𝕜 E := hTsymm.eigenvectorBasis hn
  let x_repr : EuclideanSpace 𝕜 (Fin n) := base.repr x
  apply Iff.intro
  · intro hx
    let diag : Finset (Fin n × Fin n) := Finset.univ.filter fun i ↦ i.1 = i.2
    have : RCLike.re (inner 𝕜 (T x) x) = ∑ i, ‖base.repr x i‖ ^ 2 * hTsymm.eigenvalues hn i := calc
      RCLike.re (inner 𝕜 (T x) x)
        = RCLike.re (inner 𝕜 (T (∑ i, base.repr x i • base i)) (∑ i, base.repr x i • base i)) := by rw [OrthonormalBasis.sum_repr base x]
      _ = RCLike.re (inner 𝕜 (∑ i, T (base.repr x i • base i)) (∑ i, base.repr x i • base i)) := by rw [map_sum T _ Finset.univ]
      _ = ∑ i, ∑ j, RCLike.re (inner 𝕜 (base.repr x j • T (base j)) (base.repr x i • base i)) := by simp [inner_sum, sum_inner]
      _ = ∑ i, ∑ j, RCLike.re (starRingEnd 𝕜 (base.repr x j) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn j) * (base.repr x i * inner 𝕜 (base j) (base i)))
        ) := by
          apply Fintype.sum_congr _ _
          intro i
          apply Fintype.sum_congr _ _
          intro j
          rw [hTsymm.apply_eigenvectorBasis]
          rw [InnerProductSpace.smul_left]
          rw [InnerProductSpace.smul_left]
          rw [inner_smul_right_eq_smul]
          rfl
      _ = ∑ ij : Fin n × Fin n, RCLike.re (starRingEnd 𝕜 (base.repr x ij.2) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn ij.2) * (base.repr x ij.1 * inner 𝕜 (base ij.2) (base ij.1)))
        ) := by rw [← Fintype.sum_prod_type']
      _ = ∑ ij ∈ diag, RCLike.re (starRingEnd 𝕜 (base.repr x ij.2) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn ij.2) * (base.repr x ij.1 * inner 𝕜 (base ij.2) (base ij.1)))
        ) + ∑ ij ∈ diagᶜ, RCLike.re (starRingEnd 𝕜 (base.repr x ij.2) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn ij.2) * (base.repr x ij.1 * inner 𝕜 (base ij.2) (base ij.1)))
        ) := by rw [Finset.sum_add_sum_compl diag]
      _ = ∑ ij ∈ diag, RCLike.re (starRingEnd 𝕜 (base.repr x ij.2) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn ij.2) * base.repr x ij.1)
        ) + ∑ ij ∈ diagᶜ, RCLike.re (starRingEnd 𝕜 (base.repr x ij.2) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn ij.2) * (base.repr x ij.1 * inner 𝕜 (base ij.2) (base ij.1)))
        ) := by
          have hdiag : ∀ij ∈ diag, inner 𝕜 (base ij.2) (base ij.1) = 1 := by
            intro ij hij
            unfold diag at hij
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
            rw [hij]
            have hnorm : ‖base ij.2‖ = 1 := base.norm_eq_one ij.2
            exact (inner_eq_one_iff_of_norm_one hnorm hnorm).mpr rfl
          simp +contextual [hdiag]
      _ = ∑ ij ∈ diag, RCLike.re (starRingEnd 𝕜 (base.repr x ij.2) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn ij.2) * base.repr x ij.1)
        ) := by
          have hdiagc : ∀ij ∈ diagᶜ, inner 𝕜 (base ij.2) (base ij.1) = 0 := by
            intro ij hij
            unfold diag at hij
            simp at hij
            exact base.inner_eq_zero fun heq ↦ hij (heq.symm)
          simp +contextual [hdiagc]
      _ = ∑ i, RCLike.re (starRingEnd 𝕜 (base.repr x i) *
          (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn i) * base.repr x i)
        ) := by
          let f : Fin n → Fin n → ℝ := fun i j ↦
            RCLike.re (starRingEnd 𝕜 (base.repr x j) * (starRingEnd 𝕜 ↑(hTsymm.eigenvalues hn j) * base.repr x i))
          unfold diag
          apply aux0 n f
      _ = ∑ i, RCLike.re (starRingEnd 𝕜 (base.repr x i) * base.repr x i *
          ↑(hTsymm.eigenvalues hn i)
        ) := by
          apply Fintype.sum_congr _ _
          intro i
          rw [RCLike.conj_ofReal]
          ring_nf
      _ = ∑ i, RCLike.re ((‖base.repr x i‖ : 𝕜)^2 * ↑(hTsymm.eigenvalues hn i)) := by
          simp +contextual [RCLike.conj_mul]
      _ = ∑ i, (‖base.repr x i‖^2 * hTsymm.eigenvalues hn i) := by
          apply Fintype.sum_congr _ _
          intro i
          rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
    rw [this] at hx
    have : ∀i, 0 ≤ ‖base.repr x i‖ ^ 2 * hTsymm.eigenvalues hn i := by
      intro i
      rw [mul_nonneg_iff]
      apply Or.inl
      apply And.intro
      · exact sq_nonneg ‖base.repr x i‖
      · exact hT.nonneg_eigenvalues i
    rw [Fintype.sum_eq_zero_iff_of_nonneg this] at hx
    rw [funext_iff] at hx
    simp only [Pi.zero_apply, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at hx
    rw [← base.sum_repr x]
    rw [map_sum T _ Finset.univ]
    simp only [map_smul]
    simp_rw [base, hTsymm.apply_eigenvectorBasis]
    simp +contextual only  [smul_smul]
    apply Fintype.sum_eq_zero
    intro i
    apply smul_eq_zero_of_left
    have hxi : base.repr x i = 0 ∨ hTsymm.eigenvalues hn i = 0 := hx i
    apply hxi.elim
    · intro hxi0
      exact mul_eq_zero_of_left hxi0 ↑(hTsymm.eigenvalues hn i)
    · intro hxi0
      apply mul_eq_zero_of_right
      exact RCLike.ofReal_eq_zero.mpr hxi0
  · intro hx
    rw [hx]
    simp

omit [CompleteSpace E] in
theorem isPositiveSemiDefinite.inner_app_eq_zero_iff_app_eq_zero {T : E →ₗ[𝕜]E} (hT : T.isPositiveSemiDefinite) (x : E) :
    inner 𝕜 (T x) x = 0 ↔ T x = 0 := by
  apply Iff.intro
  · intro hx
    have hx' : RCLike.re (inner 𝕜 (T x) x) = 0 := by
      rw [hx]
      exact RCLike.zero_re'
    exact (re_inner_app_eq_zero_iff_app_eq_zero hT x).mp hx'
  · intro hx
    rw [hx]
    simp

end LinearMap
