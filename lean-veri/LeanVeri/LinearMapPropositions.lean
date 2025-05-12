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


lemma isPositiveSemiDefinite_add_of_isPositiveSemiDefinite (T S : E →ₗ[𝕜] E) (hT : T.isPositiveSemiDefinite)
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

lemma real_eigenvalues_of_IsSymmetric (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) (i : Fin (Module.finrank 𝕜 E)) :
    0 ≤ hT.eigenvalues rfl i := by
  have hT' : IsSelfAdjoint T := (isSymmetric_iff_isSelfAdjoint T).mp hT
  let x : E := hT.eigenvectorBasis rfl i
  let l : 𝕜 := hT.eigenvalues rfl i
  have : starRingEnd 𝕜 l = l := RCLike.conj_ofReal (hT.eigenvalues rfl i)
  have hinnerT : inner 𝕜 (T x) x = l * inner 𝕜 x x := by
    rw [hT]
    rw [IsSymmetric.apply_eigenvectorBasis]
    rw [inner_smul_right_eq_smul]
    unfold l x
    simp
  have hinnerT' : inner 𝕜 (T x) x = starRingEnd 𝕜 l * inner 𝕜 x x := by
    rw [IsSymmetric.apply_eigenvectorBasis]
    rw [InnerProductSpace.smul_left]
  sorry


example (n : ℕ) (f : Fin n → Fin n → ℝ) :
    ∑(i₀ : Fin n), ∑(i₁ : Fin n), f i₀ i₁ =
      (∑(i₀ : Fin n), ∑(i₁ : Fin n), (if i₀ ≠ i₁ then f i₀ i₁ else 0)) + (∑(i : Fin n), f i i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_ite]
  rw [← Finset.sum_add_sum_compl {y | x ≠ y}]
  simp
  conv => rhs; rw [← Finset.sum_singleton (f x ·) x]
  convert rfl
  -- remaining goal: `{x} = {x_1 | x = x_1}`
  -- might be easier than what follows
  ext i
  rw [Finset.mem_singleton]
  rw [Finset.mem_filter]
  exact ⟨(⟨Finset.mem_univ i, ·.symm⟩), (·.2.symm)⟩
/-
example (x : 𝕜) (y : ℝ) (hxy : x = 0 ∨ y = 0) : x * y = 0 := by
  apply hxy.elim
  · intro hx0
    apply?
    sorry
  · sorry -/

lemma aux0 (n : ℕ) (f : Fin n → Fin n → 𝕜) :
    ∑i ∈ ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2), f i.1 i.2 =
    ∑i, f i i := by
  let diag := (@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2
  rw [← Lean.Grind.CommRing.add_zero (∑i ∈ ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2), f i.1 i.2)]

  have hdiag : ∑i ∈ diagᶜ, 0 = 0 := by
    exact Finset.sum_const_zero
  rw [← show ∑i ∈ diagᶜ, (0 : 𝕜) = 0 by exact Finset.sum_const_zero]
  have diagc : diagᶜ = ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ ¬i.1 = i.2) := by
    unfold diag
    simp
  rw [diagc]

  rw [← Finset.sum_ite]
  rw [Fintype.sum_prod_type]
  --apply Finset.sum_congr rfl
  --intro x _
  simp


lemma aux1 (n : ℕ) (f : Fin n → ℝ) (hf : ∀i, 0 ≤ f i) : ∑i, f i = 0 ↔ ∀i, f i = 0 := by
  rw [propext (Fintype.sum_eq_zero_iff_of_nonneg hf)]
  sorry

lemma aux'' (T : E →ₗ[𝕜]E) (hT : T.isPositiveSemiDefinite) (x : E) :
    RCLike.re (inner 𝕜 (T x) x) = 0 ↔ T x = 0 := by
  have hTsymm : T.IsSymmetric := (isSymmetric_iff_isSelfAdjoint T).mpr hT.left
  let n : ℕ := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  let base : OrthonormalBasis (Fin n) 𝕜 E := hTsymm.eigenvectorBasis hn
  let x_repr : EuclideanSpace 𝕜 (Fin n) := base.repr x
  apply Iff.intro
  · intro hx
    rw [← OrthonormalBasis.sum_repr base x] at hx
/-     have : (T (∑ i, base.repr x i • base i)) = ∑ i, T (base.repr x i • base i) := by
      exact map_sum T _ Finset.univ -/
    have hi : ∀i, T (base.repr x i • base i) = base.repr x i • T (base i) := by
      exact fun i ↦ CompatibleSMul.map_smul T (base.repr x i) (base i)
    rw [map_sum T _ Finset.univ] at hx
    --rw [Fintype.sum_congr _ _ hi] at hx
    --have hbase : ∀ i, T (base i) = (hTsymm.eigenvalues hn i : 𝕜) • base i := by
    --  exact fun i ↦ IsSymmetric.apply_eigenvectorBasis hTsymm hn i
    --have hbase' : ∀ i, base.repr x i • T (base i) = base.repr x i • (hTsymm.eigenvalues hn i : 𝕜) • base i := by
    --  exact fun i ↦ congrArg (HSMul.hSMul (base.repr x i)) (hbase i)
    --rw [Fintype.sum_congr _ _ hbase'] at hx
    --have : inner 𝕜 x (∑ i, base i) = ∑ i, inner 𝕜 x (base i) := by
    --  exact inner_sum Finset.univ (⇑base) x
    --rw [sum_inner (Finset.univ)] at hx
    --simp at hx
    --rw [inner_sum Finset.univ] at hx
    simp [inner_sum, sum_inner] at hx
    have : ∀i0, ∀i1, RCLike.re (inner 𝕜 (base.repr x i1 • T (base i1)) (base.repr x i0 • base i0)) =
        RCLike.re ((starRingEnd 𝕜) (base.repr x i1) *
            ((starRingEnd 𝕜) ↑(hTsymm.eigenvalues hn i1) *
              (base.repr x i0 * inner 𝕜 ((hTsymm.eigenvectorBasis hn) i1) (base i0)))) := by
      intro i0 i1
      rw [IsSymmetric.apply_eigenvectorBasis]
      rw [InnerProductSpace.smul_left]
      rw [InnerProductSpace.smul_left]
      rw [inner_smul_right_eq_smul]
      rfl
    have := fun i0 ↦ Fintype.sum_congr _ _ (this i0)
    simp_rw [this] at hx
    --simp at hx
    --have : ∀y : E, RCLike.re (inner 𝕜 x y) = inner ℝ x y := sorry
    have : ∀c : 𝕜, ∀b : 𝕜, c * b = c • b := by
      exact fun c b ↦ rfl
    rw [← Fintype.sum_prod_type'] at hx
    let diag : Finset (Fin n × Fin n) := Finset.univ.filter fun i ↦ i.1 = i.2
    rw [← Finset.sum_add_sum_compl diag] at hx
    unfold base at hx
/-     have hdiag : ∀i ∈ diag, RCLike.re
        ((starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x i.2) *
          ((starRingEnd 𝕜) ↑(hTsymm.eigenvalues hn i.2) *
            ((hTsymm.eigenvectorBasis hn).repr x i.1 *
              inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1)))) =
        RCLike.re ((starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x i.2) *
          ((starRingEnd 𝕜) ↑(hTsymm.eigenvalues hn i.2) *
            ((hTsymm.eigenvectorBasis hn).repr x i.1)))
               := by
      intro i hi
      unfold diag at hi
      simp at hi
      have hnorm : ‖(hTsymm.eigenvectorBasis hn) i.2‖ = 1 := OrthonormalBasis.norm_eq_one (hTsymm.eigenvectorBasis hn) i.2
      have hinnet : inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1) = 1 := by
        rw [hi]
        exact (inner_eq_one_iff_of_norm_one hnorm hnorm).mpr rfl
      rw [hinnet]
      simp -/
    --simp_rw [hdiag] at hx
    --unfold diag at hx
    have hdiag : ∀i ∈ diag, inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1) = 1:= by
      intro i hi
      unfold diag at hi
      simp at hi
      rw [hi]
      have hnorm : ‖(hTsymm.eigenvectorBasis hn) i.2‖ = 1 := OrthonormalBasis.norm_eq_one (hTsymm.eigenvectorBasis hn) i.2
      exact (inner_eq_one_iff_of_norm_one hnorm hnorm).mpr rfl
    simp +contextual only [hdiag] at hx
    have hdiagc : ∀i ∈ diagᶜ, inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1) = 0 := by
      intro i hi
      unfold diag at hi
      simp at hi
      exact OrthonormalBasis.inner_eq_zero (hTsymm.eigenvectorBasis hn) fun a ↦ hi (Eq.symm a)
    simp +contextual only [hdiagc] at hx
    simp only [RCLike.conj_ofReal, mul_one, RCLike.conj_re, RCLike.ofReal_re, RCLike.ofReal_im,
      zero_mul, sub_zero, RCLike.conj_im, RCLike.mul_im, add_zero, neg_mul, sub_neg_eq_add, mul_zero, map_zero,
      Finset.sum_const_zero] at hx
    have hdiag' : ∀i ∈ diag, i.1 = i.2 := by
      intro i hi
      unfold diag at hi
      simp at hi
      exact hi
    --simp_rw [hdiag'] at hx
    unfold diag at hx
    let f : Fin n → Fin n → ℝ := fun i j ↦
      RCLike.re
      ((starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x j) *
        (↑(hTsymm.eigenvalues hn j) * (hTsymm.eigenvectorBasis hn).repr x i))
    have hf_def : ∀ij : Fin n × Fin n, f ij.1 ij.2 = RCLike.re
        ((starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x ij.2) *
          (↑(hTsymm.eigenvalues hn ij.2) * (hTsymm.eigenvectorBasis hn).repr x ij.1)) := by
      intro ij
      rfl
    simp +contextual only [← hf_def] at hx
    rw [aux0] at hx
    unfold f at hx
    have : ∀i, (starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x i) *
        (↑(hTsymm.eigenvalues hn i) * (hTsymm.eigenvectorBasis hn).repr x i)
          = (starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x i) *
            (hTsymm.eigenvectorBasis hn).repr x i * (↑(hTsymm.eigenvalues hn i)) := by
      intro i
      rw [mul_comm (↑(hTsymm.eigenvalues hn i)) ((hTsymm.eigenvectorBasis hn).repr x i)]
      rw [mul_assoc]
    simp +contextual only [this] at hx
    simp +contextual only [RCLike.conj_mul] at hx
    simp +contextual only [← RCLike.ofReal_pow] at hx
    simp +contextual only [← RCLike.ofReal_mul] at hx
    simp +contextual only [RCLike.ofReal_re] at hx
    have : ∀i, 0 ≤ ‖(hTsymm.eigenvectorBasis hn).repr x i‖ ^ 2 * hTsymm.eigenvalues hn i := by
      intro i
      rw [mul_nonneg_iff]
      apply Or.inl
      apply And.intro
      · exact sq_nonneg ‖(hTsymm.eigenvectorBasis hn).repr x i‖
      · exact real_eigenvalues_of_IsSymmetric T hTsymm i
    rw [Fintype.sum_eq_zero_iff_of_nonneg this] at hx
    rw [funext_iff] at hx
    simp at hx

    rw [← OrthonormalBasis.sum_repr base x]
    rw [map_sum T _ Finset.univ]
    simp only [map_smul]
    unfold base
    simp_rw [IsSymmetric.apply_eigenvectorBasis hTsymm]
    simp +contextual only  [smul_smul]
    apply Fintype.sum_eq_zero
    intro i
    apply smul_eq_zero_of_left
    have hxi := hx i
    apply hxi.elim
    · intro hxi0
      exact mul_eq_zero_of_left hxi0 ↑(hTsymm.eigenvalues hn i)
    · intro hxi0
      apply mul_eq_zero_of_right
      exact RCLike.ofReal_eq_zero.mpr hxi0
  · intro hx
    rw [hx]
    simp


lemma aux''' (T : E →ₗ[𝕜]E) (hT : T.isPositiveSemiDefinite) (x : E) :
    inner 𝕜 (T x) x = 0 ↔ T x = 0 := by
  have hTsymm : T.IsSymmetric := (isSymmetric_iff_isSelfAdjoint T).mpr hT.left
  let n : ℕ := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  let base : OrthonormalBasis (Fin n) 𝕜 E := hTsymm.eigenvectorBasis hn
  let x_repr : EuclideanSpace 𝕜 (Fin n) := base.repr x
  apply Iff.intro
  · intro hx
    rw [← OrthonormalBasis.sum_repr base x] at hx
/-     have : (T (∑ i, base.repr x i • base i)) = ∑ i, T (base.repr x i • base i) := by
      exact map_sum T _ Finset.univ -/
/-     have hinner : inner 𝕜 (T (∑ i, base.repr x i • base i)) (∑ i, base.repr x i • base i) = 0 := by
      rw [hTsymm]
      rw [map_sum T _ Finset.univ]
      simp [inner_sum, sum_inner]
      unfold base
      simp +contextual [IsSymmetric.apply_eigenvectorBasis]
      simp [inner_smul_right]
      sorry -/
    have hi : ∀i, T (base.repr x i • base i) = base.repr x i • T (base i) := by
      exact fun i ↦ CompatibleSMul.map_smul T (base.repr x i) (base i)
    rw [map_sum T _ Finset.univ] at hx
    --rw [Fintype.sum_congr _ _ hi] at hx
    --have hbase : ∀ i, T (base i) = (hTsymm.eigenvalues hn i : 𝕜) • base i := by
    --  exact fun i ↦ IsSymmetric.apply_eigenvectorBasis hTsymm hn i
    --have hbase' : ∀ i, base.repr x i • T (base i) = base.repr x i • (hTsymm.eigenvalues hn i : 𝕜) • base i := by
    --  exact fun i ↦ congrArg (HSMul.hSMul (base.repr x i)) (hbase i)
    --rw [Fintype.sum_congr _ _ hbase'] at hx
    --have : inner 𝕜 x (∑ i, base i) = ∑ i, inner 𝕜 x (base i) := by
    --  exact inner_sum Finset.univ (⇑base) x
    --rw [sum_inner (Finset.univ)] at hx
    --simp at hx
    --rw [inner_sum Finset.univ] at hx
    simp [inner_sum, sum_inner] at hx
    have : ∀i0, ∀i1, inner 𝕜 (base.repr x i1 • T (base i1)) (base.repr x i0 • base i0) =
        ((starRingEnd 𝕜) (base.repr x i1)) * (base.repr x i0 * (↑(hTsymm.eigenvalues hn i0)
            * inner 𝕜 (base i1) ((hTsymm.eigenvectorBasis hn) i0))) := by
      intro i0 i1
      rw [InnerProductSpace.smul_left]
      rw [inner_smul_right]
      rw [hTsymm]
      rw [IsSymmetric.apply_eigenvectorBasis]
      rw [inner_smul_right]
    have := fun i0 ↦ Fintype.sum_congr _ _ (this i0)
    simp_rw [this] at hx
    --simp at hx
    --have : ∀y : E, RCLike.re (inner 𝕜 x y) = inner ℝ x y := sorry
    have : ∀c : 𝕜, ∀b : 𝕜, c * b = c • b := by
      exact fun c b ↦ rfl
    rw [← Fintype.sum_prod_type'] at hx
    let diag : Finset (Fin n × Fin n) := Finset.univ.filter fun i ↦ i.1 = i.2
    rw [← Finset.sum_add_sum_compl diag] at hx
    unfold base at hx
/-     have hdiag : ∀i ∈ diag, RCLike.re
        ((starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x i.2) *
          ((starRingEnd 𝕜) ↑(hTsymm.eigenvalues hn i.2) *
            ((hTsymm.eigenvectorBasis hn).repr x i.1 *
              inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1)))) =
        RCLike.re ((starRingEnd 𝕜) ((hTsymm.eigenvectorBasis hn).repr x i.2) *
          ((starRingEnd 𝕜) ↑(hTsymm.eigenvalues hn i.2) *
            ((hTsymm.eigenvectorBasis hn).repr x i.1)))
               := by
      intro i hi
      unfold diag at hi
      simp at hi
      have hnorm : ‖(hTsymm.eigenvectorBasis hn) i.2‖ = 1 := OrthonormalBasis.norm_eq_one (hTsymm.eigenvectorBasis hn) i.2
      have hinnet : inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1) = 1 := by
        rw [hi]
        exact (inner_eq_one_iff_of_norm_one hnorm hnorm).mpr rfl
      rw [hinnet]
      simp -/
    --simp_rw [hdiag] at hx
    --unfold diag at hx
    have hdiag : ∀i ∈ diag, inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1) = 1:= by
      intro i hi
      unfold diag at hi
      simp at hi
      rw [hi]
      have hnorm : ‖(hTsymm.eigenvectorBasis hn) i.2‖ = 1 := OrthonormalBasis.norm_eq_one (hTsymm.eigenvectorBasis hn) i.2
      exact (inner_eq_one_iff_of_norm_one hnorm hnorm).mpr rfl
    simp +contextual only [hdiag] at hx
    have hdiagc : ∀i ∈ diagᶜ, inner 𝕜 ((hTsymm.eigenvectorBasis hn) i.2) ((hTsymm.eigenvectorBasis hn) i.1) = 0 := by
      intro i hi
      unfold diag at hi
      simp at hi
      exact OrthonormalBasis.inner_eq_zero (hTsymm.eigenvectorBasis hn) fun a ↦ hi (Eq.symm a)
    simp +contextual only [hdiagc] at hx
    simp only [RCLike.conj_ofReal, mul_one, RCLike.conj_re, RCLike.ofReal_re, RCLike.ofReal_im,
      zero_mul, sub_zero, RCLike.conj_im, RCLike.mul_im, add_zero, neg_mul, sub_neg_eq_add, mul_zero, map_zero,
      Finset.sum_const_zero] at hx

    have hdiag' : ∀i ∈ diag, i.1 = i.2 := by
      intro i hi
      unfold diag at hi
      simp at hi
      exact hi
    --simp_rw [hdiag'] at hx
    rw [← OrthonormalBasis.sum_repr base x]
    rw [map_sum T _ Finset.univ]
    simp only [map_smul]
    unfold base
    simp_rw [IsSymmetric.apply_eigenvectorBasis hTsymm]


    sorry
  · intro hx
    rw [hx]
    simp

/-
(a + bi) * (a' + b'i) + (a1 + b1i) * (a1' + b1'i) = 0
a * a' - b * b' + (ab' + ba')i + a1 * a1' - b1 * b1' + (a1b1' + b1a1')i = 0



(a - bi) * (a' + b'i) + (a1 - b1i) * (a1' + b1'i) = 0
a * a' + b * b' + (ab' - ba')i + a1 * a1' + b1 * b1' + (a1b1' - b1a1')i = 0

-/



lemma aux' (x y : 𝕜) (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y = 0) : x = 0 := by
  rw [propext (add_eq_zero_iff_of_nonneg hx hy)] at hsum
  sorry

lemma aux (T S : E →ₗ[𝕜] E) (hT : T.isPositiveSemiDefinite) (hS : S.isPositiveSemiDefinite) (x : E)
    (hx : (T + S) x = 0) : T x = 0 ∧ S x = 0 := by
  have hinner : RCLike.re (inner 𝕜 (T x) x) + RCLike.re (inner 𝕜 (S x) x) = 0 := by
    rw [← AddMonoidHom.map_add RCLike.re]
    rw [← inner_add_left]
    rw [← add_apply]
    rw [hx]
    simp
  have hTinner : 0 ≤ RCLike.re (inner 𝕜 (T x) x) := hT.right x
  have hSinner : 0 ≤ RCLike.re (inner 𝕜 (S x) x) := hS.right x
  rw [propext (add_eq_zero_iff_of_nonneg hTinner hSinner)] at hinner


  apply And.intro
  ·

    sorry
  · sorry


end LinearMap
