/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison, Jam Khan
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace

import LeanVeri.Sum

open scoped ComplexOrder

/-!
# Some basic propositions about `LinearMap`

This file contains some basic propositions about `LinearMap` that are not already in Mathlib.
Some of this may be later added to Mathlib.

We use `inner 𝕜 (T x) x` in several places, this is what in quantum is some times denotes as `⟨x|T|x⟩`.
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
  (N - T).isPositiveSemiDefinite

/-- Pure state operators. -/
def isPureState (T : E →ₗ[𝕜] E) : Prop :=
  T.isDensityOperator ∧ T.rank = 1

omit [CompleteSpace E]

lemma isPositiveSemiDefinite.zero : (0 : E →ₗ[𝕜] E).isPositiveSemiDefinite := by
  apply And.intro
  · exact IsSelfAdjoint.zero (E →ₗ[𝕜] E)
  · intro x
    simp [zero_apply]

lemma isPositiveSemiDefinite.one : (1 : E →ₗ[𝕜] E).isPositiveSemiDefinite := by
  apply And.intro
  · exact (isSymmetric_iff_isSelfAdjoint 1).mp fun x ↦ congrFun rfl
  · intro x
    exact inner_self_nonneg

lemma isProjection.zero : (0 : E →ₗ[𝕜] E).isProjection := And.intro isPositiveSemiDefinite.zero rfl

lemma isProjection.one : (1 : E →ₗ[𝕜] E).isProjection := And.intro isPositiveSemiDefinite.one rfl

lemma isProjection.apply_range {T : E →ₗ[𝕜] E} (hT : T.isProjection) {x : E} (hx : x ∈ range T) :
    T x = x := by
  obtain ⟨y, hy⟩ := hx
  rw [← hy, ← comp_apply, hT.right]

lemma isPositiveSemiDefinite.IsSymmetric (T : E →ₗ[𝕜] E) (hT : T.isPositiveSemiDefinite) : T.IsSymmetric :=
  (isSymmetric_iff_isSelfAdjoint T).mpr hT.left

lemma isPositiveSemiDefinite_add_of_isPositiveSemiDefinite {T S : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite)
    (hS : S.isPositiveSemiDefinite) : (T + S).isPositiveSemiDefinite := by
  apply And.intro
  · unfold IsSelfAdjoint
    rw [star_add, hT.left, hS.left]
  · intro x
    rw [add_apply, inner_add_left, AddMonoidHom.map_add]
    exact Left.add_nonneg (hT.right x) (hS.right x)

lemma isPositiveSemiDefinite_real_smul_of_isPositiveSemiDefinite {T : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite) {c : ℝ}
    (hc : 0 ≤ c) : ((c : 𝕜) • T).isPositiveSemiDefinite := by
  apply And.intro
  · rw [← isSymmetric_iff_isSelfAdjoint]
    apply IsSymmetric.smul (RCLike.conj_ofReal c) hT.IsSymmetric
  · intro x
    rw [smul_apply]
    rw [inner_smul_left]
    rw [RCLike.conj_ofReal]
    rw [RCLike.re_ofReal_mul]
    exact Left.mul_nonneg hc (hT.right x)

lemma isPositiveSemiDefinite_real_smul_of_isPositiveSemiDefinite' {c : 𝕜} (hc : 0 ≤ c) {T : E →ₗ[𝕜] E}
    (hT : T.isPositiveSemiDefinite)  : (c • T).isPositiveSemiDefinite := by
  let c' : ℝ := RCLike.re c
  have hstarc : (starRingEnd 𝕜) c = c := by
    rw [RCLike.conj_eq_iff_im]
    simp [← (RCLike.le_iff_re_im.mp hc).right]
  have hcc' : c = c' := by
    rw [RCLike.ext_iff]
    apply And.intro
    · simp [c']
    · simp only [RCLike.ofReal_im, c']
      exact RCLike.conj_eq_iff_im.mp hstarc
  have hc' : 0 ≤ c' := by
    rw [← @RCLike.zero_re 𝕜]
    exact (RCLike.le_iff_re_im.mp hc).left
  rw [hcc']
  exact isPositiveSemiDefinite_real_smul_of_isPositiveSemiDefinite hT hc'

lemma isPositiveSemiDefinite.sub_of_LoewnerOrder {T S : E →ₗ[𝕜] E} (h : T.LoewnerOrder S) :
    (S - T).isPositiveSemiDefinite := by
  apply And.intro
  · rw [← isSymmetric_iff_isSelfAdjoint]
    exact h.IsSymmetric
  · exact h.right

lemma isPositiveSemiDefinite.nonneg_real_smul {T : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite)
    {c : ℝ} (hc : 0 ≤ c) : ((c : 𝕜) • T).isPositiveSemiDefinite := by
  apply And.intro
  · rw [← isSymmetric_iff_isSelfAdjoint]
    exact IsSymmetric.smul (RCLike.conj_ofReal c) hT.IsSymmetric
  · intro x
    rw [smul_apply, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
    exact Left.mul_nonneg hc (hT.right x)

lemma isPositiveSemiDefinite.nonneg_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite)
    (i : Fin (Module.finrank 𝕜 E)) : 0 ≤ hT.IsSymmetric.eigenvalues rfl i := by
  have h := hT.right (hT.IsSymmetric.eigenvectorBasis rfl i)
  rw [hT.IsSymmetric.apply_eigenvectorBasis, inner_smul_real_left, RCLike.smul_re,
    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one] at h
  simp only [one_pow, mul_one] at h
  exact h

omit [FiniteDimensional 𝕜 E] in
lemma eq_zero_iff_forall_re_inner_eq_zero (T : E →ₗ[𝕜]E) :
    T = 0 ↔ ∀x : E, ∀y : E, RCLike.re (inner 𝕜 (T x) y) = 0 := by
  apply Iff.intro
  · intro h
    simp [h]
  · intro h
    apply LinearMap.ext
    intro x
    have hTx := h x (T x)
    rw [inner_self_eq_norm_mul_norm, mul_self_eq_zero] at hTx
    exact norm_eq_zero.mp hTx

lemma IsSelfAdjoint.re_inner_app_self_eq_zero_iff_app_eq_zero {T : E →ₗ[𝕜]E} (hT : IsSelfAdjoint T) :
    T = 0 ↔ ∀x : E, RCLike.re (inner 𝕜 (T x) x) = 0 := by
  apply Iff.intro
  · intro h
    simp [h]
  · intro h
    have aux : ∀x : E, ∀y : E, RCLike.re (inner 𝕜 (T x) y) = RCLike.re ((inner 𝕜 (T (x + y)) (x + y) - inner 𝕜 (T (x - y)) (x - y))) / 4 := by
      intro x y
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, map_sub, map_add, inner_re_symm (T y) x]
      rw [(isSymmetric_iff_isSelfAdjoint T).mpr hT]
      ring_nf
    have h' : ∀x : E, ∀y : E, RCLike.re (inner 𝕜 (T x) y) = 0 := by
      intro x y
      rw [aux, map_sub, h (x + y), h (x - y)]
      ring
    apply (eq_zero_iff_forall_re_inner_eq_zero T).mpr h'

lemma isPositiveSemiDefinite.eq_iff_forall_re_inner_app_self_eq {T N : E →ₗ[𝕜]E} (hT : IsSelfAdjoint T)
    (hN : IsSelfAdjoint N) :
    T = N ↔ ∀x : E, RCLike.re (inner 𝕜 (T x) x) = RCLike.re (inner 𝕜 (N x) x) := by
  have hT' : T.IsSymmetric := (isSymmetric_iff_isSelfAdjoint T).mpr hT
  have hN' : N.IsSymmetric := (isSymmetric_iff_isSelfAdjoint N).mpr hN
  have hTN : IsSelfAdjoint (T - N) := (isSymmetric_iff_isSelfAdjoint (T - N)).mp (hT'.sub hN')
  apply Iff.intro
  · intro h x
    rw [h]
  · intro h
    have hTN' : ∀x : E, RCLike.re (inner 𝕜 ((T - N) x) x) = 0 := by
      intro x
      rw [sub_apply, inner_sub_left, map_sub, sub_eq_zero]
      exact h x
    rw [← sub_eq_zero]
    exact (IsSelfAdjoint.re_inner_app_self_eq_zero_iff_app_eq_zero hTN).mpr hTN'

/--
Characterization of when `RCLike.re (inner 𝕜 (T x) x)` is zero.
The proof works be decomposing `x` in the eigenbasis of `T`.
-/
lemma isPositiveSemiDefinite.re_inner_app_eq_zero_iff_app_eq_zero {T : E →ₗ[𝕜]E} (hT : T.isPositiveSemiDefinite) (x : E) :
    RCLike.re (inner 𝕜 (T x) x) = 0 ↔ T x = 0 := by
  have hTsymm : T.IsSymmetric := hT.IsSymmetric
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
          rw [hTsymm.apply_eigenvectorBasis, InnerProductSpace.smul_left, InnerProductSpace.smul_left, inner_smul_right_eq_smul]
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
          apply sum_diag_eq n f
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
    rw [Fintype.sum_eq_zero_iff_of_nonneg this, funext_iff] at hx
    simp only [Pi.zero_apply, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at hx
    rw [← base.sum_repr x, map_sum T _ Finset.univ]
    simp only [map_smul]
    simp_rw [base, hTsymm.apply_eigenvectorBasis]
    simp +contextual only [smul_smul]
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

theorem isPositiveSemiDefinite.inner_app_eq_zero_iff_app_eq_zero {T : E →ₗ[𝕜]E} (hT : T.isPositiveSemiDefinite) (x : E) :
    inner 𝕜 (T x) x = 0 ↔ T x = 0 := by
  apply Iff.intro
  · intro hx
    have hx' : RCLike.re (inner 𝕜 (T x) x) = 0 := by
      rw [hx]
      exact RCLike.zero_re
    exact (re_inner_app_eq_zero_iff_app_eq_zero hT x).mp hx'
  · intro hx
    rw [hx]
    simp

lemma LoewnerOrder_iff_of_isPositiveSemiDefinite {T N : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite)
    (hN : N.isPositiveSemiDefinite) :
    T.LoewnerOrder N ↔ ∀x : E, 0 ≤ RCLike.re (inner 𝕜 ((N - T) x) x) := by
  apply Iff.intro
  · intro h
    exact (isPositiveSemiDefinite.sub_of_LoewnerOrder h).right
  · intro h
    exact And.intro (IsSelfAdjoint.sub hN.left hT.left) h

lemma LoewnerOrder_iff_of_isPositiveSemiDefinite' {T N : E →ₗ[𝕜] E} (hT : T.isPositiveSemiDefinite)
    (hN : N.isPositiveSemiDefinite) :
    T.LoewnerOrder N ↔ ∀x : E, RCLike.re (inner 𝕜 (T x) x) ≤ RCLike.re (inner 𝕜 (N x) x) := by
  rw [LoewnerOrder_iff_of_isPositiveSemiDefinite hT hN]
  apply forall_congr'
  intro x
  calc
    0 ≤ RCLike.re (inner 𝕜 ((N - T) x) x)
    ↔ 0 ≤ RCLike.re (inner 𝕜 (N x - T x) x) := by rfl
  _ ↔ 0 ≤ RCLike.re (inner 𝕜 (N x) x - inner 𝕜 (T x) x) := by rw [inner_sub_left]
  _ ↔ 0 ≤ RCLike.re (inner 𝕜 (N x) x) - RCLike.re (inner 𝕜 (T x) x) := by rw [map_sub]
  _ ↔ RCLike.re (inner 𝕜 (T x) x) ≤ RCLike.re (inner 𝕜 (N x) x) := by apply sub_nonneg

end LinearMap
