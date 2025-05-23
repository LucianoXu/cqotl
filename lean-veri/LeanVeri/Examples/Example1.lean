/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.Commons
import LeanVeri.InfValPred
import LeanVeri.LinearMapPropositions
import LeanVeri.OuterProduct

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]
local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)

noncomputable def A1 : InfValPred 𝕜 𝕜² :=
  {
    P := ketbraP
    X := ketbraM
    PisPos := isPositiveSemiDefinite_ketbraP
    XisProj := isProjection_ketbraM
    compPX := by
      rw [LinearMap.ext_iff]
      intro x
      simp only [LinearMap.coe_comp, Function.comp_apply]
      simp only [ketbraM, ketbraP]
      simp only [outerProduct_def]
      rw [inner_smul_right]
      unfold inner
      unfold InnerProductSpace.toInner
      unfold PiLp.innerProductSpace
      field_simp [ketM, ketP, ket0, ket1]
  }

open LinearMap in
noncomputable def A2 : InfValPred 𝕜 𝕜² :=
  let P := (1/2 : 𝕜) • 1 + ketbra0
  {
    P := P
    X := 0
    PisPos := isPositiveSemiDefinite_add_of_isPositiveSemiDefinite
      (isPositiveSemiDefinite_real_smul_of_isPositiveSemiDefinite' (one_div_nonneg.mpr zero_le_two) isPositiveSemiDefinite.one)
      isPositiveSemiDefinite_ketbra0
    XisProj := isProjection.zero
    compPX := zero_comp P
  }

lemma obligation1 : @InfValPred.LoewnerOrder 𝕜 𝕜² _ _ _ _ A2 A1 := by
  unfold InfValPred.LoewnerOrder
  intro x
  unfold InfValPred.inner_app_self
  have h2 : inner 𝕜 (A2.X x) x = 0 := by simp [show A2.X = (0 : 𝕜² →ₗ[𝕜] 𝕜²) by rfl]
  by_cases h1 : inner 𝕜 (A1.X x) x = 0 <;> simp only [h1, h2, if_true, if_false]
  · simp only [ENNReal.some_eq_coe, ENNReal.coe_le_coe]
    apply Subtype.mk_le_mk.mpr
    rw [← sub_nonneg, ← map_sub]
    apply le_of_eq
    rw [← @RCLike.zero_re' 𝕜]
    apply (RCLike.ext_iff.mp _).left
    apply Eq.symm
    obtain ⟨c, hc⟩ := exist_smul_ketP_of_inner_ketbraM_eq_zero x h1
    calc
      inner 𝕜 (A1.P x) x - inner 𝕜 (A2.P x) x
        = inner 𝕜 (ketbraP x) x - inner 𝕜 ((((1/2) • 1 + ketbra0) : 𝕜² →ₗ[𝕜] 𝕜²) x) x := rfl
      _ = inner 𝕜 ((1 - ketbraM) x) x - inner 𝕜 ((((1/2 : 𝕜) • 1 + ketbra0) : 𝕜² →ₗ[𝕜] 𝕜²) x) x := by rw [ketbraP_eq_one_sub_ketbraM]
      _ = inner 𝕜 (x - ketbraM x) x - inner 𝕜 ((1/2 : 𝕜) • x + ketbra0 x) x := rfl
      _ = inner 𝕜 x x - inner 𝕜 (ketbraM x) x - (inner 𝕜 ((1/2 : 𝕜) • x) x + inner 𝕜 (ketbra0 x) x) := by rw [inner_sub_left, inner_add_left]
      _ = inner 𝕜 x x - (inner 𝕜 ((1/2 : 𝕜) • x) x + inner 𝕜 (ketbra0 x) x) := by unfold A1 at h1; simp [h1]
      _ = inner 𝕜 x x - (starRingEnd 𝕜 (1/2) * inner 𝕜 x x + inner 𝕜 (ketbra0 x) x) := by rw [← inner_smul_left]
      _ = inner 𝕜 x x - (1/2 * inner 𝕜 x x + inner 𝕜 (ketbra0 x) x) := by simp [RCLike.conj_ofNat]
      _ = 1/2 * inner 𝕜 x x - inner 𝕜 (ketbra0 x) x := by ring_nf
      _ = 1/2 * inner 𝕜 (c • ketP) (c • ketP) - inner 𝕜 (ketbra0 (c • ketP)) (c • ketP) := by rw [hc]
      _ = 1/2 * inner 𝕜 (c • ketP) (c • ketP) - inner 𝕜 (c • ketbra0 ketP) (c • ketP) := by rw [map_smul]
      _ = 1/2 * (c * (starRingEnd 𝕜 c * @inner 𝕜 𝕜² _ ketP ketP)) - c * (starRingEnd 𝕜 c * @inner 𝕜 𝕜² _ (ketbra0 ketP) ketP) := by simp only [inner_smul_left, inner_smul_right]
      _ = 1/2 * (c * starRingEnd 𝕜 c) - c * starRingEnd 𝕜 c * @inner 𝕜 𝕜² _ (ketbra0 ketP) ketP := by simp only [mul_assoc, inner_ketP_ketP, mul_one]
      _ = 1/2 * (c * starRingEnd 𝕜 c) - c * starRingEnd 𝕜 c * @inner 𝕜 𝕜² _ ((outerProduct 𝕜 ket0 ket0) ketP) ketP := rfl
      _ = 1/2 * (c * starRingEnd 𝕜 c) - c * starRingEnd 𝕜 c * (@inner 𝕜 𝕜² _ ket0 ketP * @inner 𝕜 𝕜² _ ket0 ketP) := by rw [inner_outerProduct_eq_inner_mul_inner]
      _ = 1/2 * (c * starRingEnd 𝕜 c) - c * starRingEnd 𝕜 c * (1/√2 * (1/√2)) := by rw [inner_ket0_ketP]
      _ = 1/2 * (c * starRingEnd 𝕜 c) - c * starRingEnd 𝕜 c * (1/2) := by rw [show (1 : 𝕜)/√2 * (1/√2) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
      _ = 0 := by ring_nf
  · apply OrderTop.le_top
