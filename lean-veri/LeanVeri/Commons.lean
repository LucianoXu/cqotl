/-
Copyright (c) 2025 Iván Renison, Jam Khan. All rights reserved.
Authors: Iván Renison, Jam Khan
-/
import LeanVeri.LinearMapPropositions
import LeanVeri.OuterProduct
import LeanVeri.Projection
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection
/-!
Some vectors and linear maps that are commonly used in quantum computing.
-/

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)


/-- Ket zero, usually denoted as |0⟩. -/
def ket0 : 𝕜² := !₂[1, 0]

/-- Ket one, usually denoted as |1⟩. -/
def ket1 : 𝕜² := !₂[0, 1]

/-- Ket plus, usually denoted as |+⟩. -/
noncomputable def ketP : 𝕜² := (1/√2 : 𝕜) • (ket0 + ket1)

/-- Ket minus, usually denoted as |-⟩. -/
noncomputable def ketM : 𝕜² := (1/√2 : 𝕜) • (ket0 - ket1)

/-- Ket one times bra one, usually denoted as |1⟩⟨1|. -/
def ketbra1 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket1 ket1

/-- Ket one times bra one, usually denoted as |1⟩⟨0|. -/
def ket1bra0 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket1 ket0

/-- Ket one times bra one, usually denoted as |0⟩⟨1|. -/
def ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket0 ket1

/-- Ket zero times bra zero, usually denoted as |0⟩⟨0|. -/
def ketbra0 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket0 ket0

/-- Ket plus times bra plus, usually denoted as |+⟩⟨+|. -/
noncomputable def ketbraP : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketP ketP

/-- Ket minus times bra minus, usually denoted as |-⟩⟨-|. -/
noncomputable def ketbraM : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketM ketM

noncomputable def ketPbraM : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketP ketM

noncomputable def ketMbraP : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketM ketP

noncomputable def Hadamard : 𝕜² →ₗ[𝕜] 𝕜² := outerProduct 𝕜 ket0 ketP + outerProduct 𝕜 ket1 ketM

/-- Ket plus equals !₂[1/√2, 1/√2] -/
lemma ketP_eq : ketP = (!₂[1/√2, 1/√2] : 𝕜²) := by
  unfold ketP ket0 ket1
  simp [← WithLp.equiv_symm_add, ← WithLp.equiv_symm_smul]

/-- Ket minus equals !₂[1/√2, -1/√2] -/
lemma ketM_eq : ketM = (!₂[1/√2, -1/√2] : 𝕜²) := by
  unfold ketM ket0 ket1
  simp only [← WithLp.equiv_symm_sub, ← WithLp.equiv_symm_smul]
  field_simp

/-- ‖|0⟩‖ = 1 -/
lemma norm_ket0 : @norm 𝕜² _ ket0 = 1 := by
  unfold norm PiLp.instNorm
  simp [ket0]

/-- ‖|1⟩‖ = 1 -/
lemma norm_ket1 : @norm 𝕜² _ ket1 = 1 := by
  unfold norm PiLp.instNorm
  simp [ket1]

/-- ‖|+⟩‖ = 1 -/
lemma norm_ketP : @norm 𝕜² _ ketP = 1 := by
  unfold norm PiLp.instNorm
  field_simp [ketP, ket0, ket1]

/-- ‖|-⟩‖ = 1 -/
lemma norm_ketM : @norm 𝕜² _ ketM = 1 := by
  unfold norm PiLp.instNorm
  field_simp [ketM, ket0, ket1]

/-- (|0⟩⟨0|)† = |0⟩⟨0| -/
lemma isSelfAdjoint_ketbra0 : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbra0 :=
  IsSelfAdjoint_outerProduct_self 𝕜 ket0

/-- (|1⟩⟨1|)† = |1⟩⟨1| -/
lemma isSelfAdjoint_ketbra1 : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbra1 :=
  IsSelfAdjoint_outerProduct_self 𝕜 ket1

/-- (|+⟩⟨+|)† = |+⟩⟨+| -/
lemma isProjection_ketbraP : @LinearMap.isProjection 𝕜 𝕜² _ _ _ _ ketbraP :=
  isProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ketP

/-- (|-⟩⟨-|)† = |-⟩⟨-| -/
lemma isProjection_ketbraM : @LinearMap.isProjection 𝕜 𝕜² _ _ _ _ ketbraM :=
  isProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ketM


/-- ⟨0|0⟩ = 1 -/
lemma inner_ket0_ket0 : @inner 𝕜 𝕜² _ ket0 ket0 = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ket0 norm_ket0).mpr rfl

/-- ⟨1|1⟩ = 1 -/
lemma inner_ket1_ket1 : @inner 𝕜 𝕜² _ ket1 ket1 = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ket1 norm_ket1).mpr rfl

/-- ⟨0|1⟩ = 0 -/
lemma inner_ket0_ket1 : @inner 𝕜 𝕜² _ ket0 ket1 = 0 := by
  unfold ket0 ket1
  simp only [PiLp.inner_apply, WithLp.equiv_symm_pi_apply, RCLike.inner_apply, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, map_one, mul_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_zero, mul_zero, add_zero]

/-- ⟨1|0⟩ = 0 -/
lemma inner_ket1_ket0 : @inner 𝕜 𝕜² _ ket1 ket0 = 0 := by
  unfold ket1 ket0
  simp only [PiLp.inner_apply, WithLp.equiv_symm_pi_apply, RCLike.inner_apply, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, map_zero, mul_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_one, mul_one, add_zero]

/-- ⟨+|+⟩ = 1 -/
lemma inner_ketP_ketP : @inner 𝕜 𝕜² _ ketP ketP = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ketP norm_ketP).mpr rfl

/-- ⟨-|-⟩ = 1 -/
lemma inner_ketM_ketM : @inner 𝕜 𝕜² _ ketM ketM = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ketM norm_ketM).mpr rfl

lemma neZero_ket0 : NeZero (R := 𝕜²) ket0 := by
  rw [neZero_iff, ← norm_pos_iff, norm_ket0]
  exact Real.zero_lt_one

lemma neZero_ket1 : NeZero (R := 𝕜²) ket1 := by
  rw [neZero_iff, ← norm_pos_iff, norm_ket1]
  exact Real.zero_lt_one

lemma neZero_ketP : NeZero (R := 𝕜²) ketP := by
  rw [neZero_iff, ← norm_pos_iff, norm_ketP]
  exact Real.zero_lt_one

lemma neZero_ketM : NeZero (R := 𝕜²) ketM := by
  rw [neZero_iff, ← norm_pos_iff, norm_ketM]
  exact Real.zero_lt_one

/-- |0⟩⟨0| is PSD (Positive Semi-Definitie) -/
lemma isPositiveSemiDefinite_ketbra0 : @LinearMap.isPositiveSemiDefinite 𝕜 𝕜² _ _ _ _ ketbra0 :=
  isPositiveSemiDefinite_outerProduct_self 𝕜 ket0

/-- |1⟩⟨1| is PSD -/
lemma isPositiveSemiDefinite_ketbra1 : @LinearMap.isPositiveSemiDefinite 𝕜 𝕜² _ _ _ _ ketbra1 :=
  isPositiveSemiDefinite_outerProduct_self 𝕜 ket1

/-- (|0⟩⟨0|)² = |0⟩⟨0| -/
lemma isProjection_ketbra0 : @LinearMap.isProjection 𝕜 𝕜² _ _ _ _ ketbra0 :=
  isProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ket0

/-- (|1⟩⟨1|)² = |1⟩⟨1| -/
lemma isProjection_ketbra1 : @LinearMap.isProjection 𝕜 𝕜² _ _ _ _ ketbra1 :=
  isProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ket1

/-- (|+⟩⟨+|)† = |+⟩⟨+| -/
lemma isSelfAdjoint_ketbraP : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbraP :=
  IsSelfAdjoint_outerProduct_self 𝕜 ketP

/-- (|-⟩⟨-|)† = |-⟩⟨-| -/
lemma isSelfAdjoint_ketbraM : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbraM :=
  IsSelfAdjoint_outerProduct_self 𝕜 ketM

/-- |+⟩⟨+| is PSD -/
lemma isPositiveSemiDefinite_ketbraP : @LinearMap.isPositiveSemiDefinite 𝕜 𝕜² _ _ _ _ ketbraP :=
  isPositiveSemiDefinite_outerProduct_self 𝕜 ketP

/-- |-⟩⟨-| is PSD -/
lemma isPositiveSemiDefinite_ketbraM : @LinearMap.isPositiveSemiDefinite 𝕜 𝕜² _ _ _ _ ketbraM :=
  isPositiveSemiDefinite_outerProduct_self 𝕜 ketM

/-- ⟨+|0⟩ = 1/√2 -/
lemma inner_ketP_ket0 : @inner 𝕜 𝕜² _ ketP ket0 = 1/√2 := by
  calc
    @inner 𝕜 𝕜² _ ketP ket0
      = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • (ket0 + ket1)) ket0                       := rfl
    _ = @inner 𝕜 𝕜² _ (((1/√2 : 𝕜) • ket0) + ((1/√2 : 𝕜) • ket1)) ket0        := by
      refine Inseparable.inner_eq_inner (Inseparable.of_eq ?_) rfl
      rw [smul_add]
    _ = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket0) ket0 +  @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket1) ket0  := by rw [inner_add_left]
    _ = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket0 +  (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket0      := by
      rw [inner_smul_left, inner_smul_left, inner_ket0_ket0, inner_ket1_ket0, mul_zero, mul_zero]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, mul_one, add_zero]
    _ = 1/√2 := by
      rw [inner_ket0_ket0, inner_ket1_ket0, mul_zero]
      simp only [one_div, mul_one, add_zero]

/-- ⟨0|+⟩ = 1/√2 -/
lemma inner_ket0_ketP : @inner 𝕜 𝕜² _ ket0 ketP = 1/√2 := by
  calc
    @inner 𝕜 𝕜² _ ket0 ketP
      = @inner 𝕜 𝕜² _ ket0 ((1/√2 : 𝕜) • (ket0 + ket1))                                 := rfl
    _ = @inner 𝕜 𝕜² _ ket0 (((1/√2 : 𝕜) • ket0) + ((1/√2 : 𝕜) • ket1))                  := by
      refine Inseparable.inner_eq_inner rfl (Inseparable.of_eq ?_)
      rw [smul_add]
    _ = @inner 𝕜 𝕜² _ ket0 ((1/√2 : 𝕜) • ket0) + @inner 𝕜 𝕜² _ ket0 ((1/√2 : 𝕜) • ket1) := by
      rw [inner_add_right]
    _ = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket0 +  (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket1    := by
      repeat rw [inner_smul_right]
    _ = 1/√2  := by
      rw [inner_ket0_ket0, inner_ket0_ket1, mul_zero, add_zero, mul_one]

/-- ⟨+|1⟩ = 1/√2 -/
lemma inner_ketP_ket1 : @inner 𝕜 𝕜² _ ketP ket1 = 1/√2 := by
  calc
    @inner 𝕜 𝕜² _ ketP ket1
      = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • (ket0 + ket1)) ket1                       := rfl
    _ = @inner 𝕜 𝕜² _ (((1/√2 : 𝕜) • ket0) + ((1/√2 : 𝕜) • ket1)) ket1        := by
      refine Inseparable.inner_eq_inner (Inseparable.of_eq ?_) rfl
      rw [smul_add]
    _ = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket0) ket1 +  @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket1) ket1  := by rw [inner_add_left]
    _ = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket1 +  (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket1      := by
      rw [inner_smul_left, inner_smul_left, inner_ket0_ket1, inner_ket1_ket1, mul_zero, mul_zero]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, mul_one, add_zero]
    _ = 1/√2 := by
      rw [inner_ket0_ket1, inner_ket1_ket1, mul_zero]
      simp only [one_div, mul_one, zero_add]

/-- ⟨1|+⟩ = 1/√2 -/
lemma inner_ket1_ketP : @inner 𝕜 𝕜² _ ket1 ketP = 1/√2 := by
  calc
    @inner 𝕜 𝕜² _ ket1 ketP = @inner 𝕜 𝕜² _ ket1 ((1/√2 : 𝕜) • (ket0 + ket1))                                 := rfl
    _                       = @inner 𝕜 𝕜² _ ket1 (((1/√2 : 𝕜) • ket0) + ((1/√2 : 𝕜) • ket1))                  := by
      refine Inseparable.inner_eq_inner rfl (Inseparable.of_eq ?_)
      rw [smul_add]
    _                       = @inner 𝕜 𝕜² _ ket1 ((1/√2 : 𝕜) • ket0) + @inner 𝕜 𝕜² _ ket1 ((1/√2 : 𝕜) • ket1) := by
      rw [inner_add_right]
    _                       = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket0 +  (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket1    := by
      repeat rw [inner_smul_right]
    _                       = 1/√2  := by
      rw [inner_ket1_ket0, inner_ket1_ket1, mul_zero, zero_add, mul_one]

/-- ⟨-|0⟩ = 1/√2 -/
lemma inner_ketM_ket0 : @inner 𝕜 𝕜² _ ketM ket0 = 1/√2 := by
  calc
    @inner 𝕜 𝕜² _ ketM ket0
      = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • (ket0 - ket1)) ket0                       := rfl
    _ = @inner 𝕜 𝕜² _ (((1/√2 : 𝕜) • ket0) - ((1/√2 : 𝕜) • ket1)) ket0        := by
      refine Inseparable.inner_eq_inner (Inseparable.of_eq ?_) rfl
      rw [smul_sub]
    _ = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket0) ket0 -  @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket1) ket0  := by rw [inner_sub_left]
    _ = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket0 +  (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket0      := by
      rw [inner_smul_left, inner_smul_left, inner_ket0_ket0, inner_ket1_ket0, mul_zero, mul_zero]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, mul_one, sub_zero, add_zero]
    _ = 1/√2 := by
      rw [inner_ket0_ket0, inner_ket1_ket0, mul_zero]
      simp only [one_div, mul_one, add_zero]

/-- ⟨0|-⟩ = 1/√2 -/
lemma inner_ket0_ketM : @inner 𝕜 𝕜² _ ket0 ketM = 1/√2 := by
  calc
    @inner 𝕜 𝕜² _ ket0 ketM
      = @inner 𝕜 𝕜² _ ket0 ((1/√2 : 𝕜) • (ket0 - ket1))                                 := rfl
    _ = @inner 𝕜 𝕜² _ ket0 (((1/√2 : 𝕜) • ket0) - ((1/√2 : 𝕜) • ket1))                  := by
      refine Inseparable.inner_eq_inner rfl (Inseparable.of_eq ?_); rw [smul_sub]
    _ = @inner 𝕜 𝕜² _ ket0 ((1/√2 : 𝕜) • ket0) - @inner 𝕜 𝕜² _ ket0 ((1/√2 : 𝕜) • ket1) := by rw [inner_sub_right]

    _ = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket0 - (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket1    := by
      repeat rw [inner_smul_right]
    _ = 1/√2  := by
      rw [inner_ket0_ket0, inner_ket0_ket1, mul_zero, sub_zero, mul_one]

/-- ⟨-|1⟩ = - 1/√2 -/
lemma inner_ketM_ket1 : @inner 𝕜 𝕜² _ ketM ket1 = - (1/√2) := by
  calc
    @inner 𝕜 𝕜² _ ketM ket1
      = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • (ket0 - ket1)) ket1                       := rfl
    _ = @inner 𝕜 𝕜² _ (((1/√2 : 𝕜) • ket0) - ((1/√2 : 𝕜) • ket1)) ket1        := by
      refine Inseparable.inner_eq_inner (Inseparable.of_eq ?_) rfl
      rw [smul_sub]
    _ = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket0) ket1 - @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • ket1) ket1  := by rw [inner_sub_left]
    _ = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket0 ket1 - (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket1      := by
      rw [inner_smul_left, inner_smul_left, inner_ket0_ket1, inner_ket1_ket1, mul_zero, mul_zero]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, mul_one, add_zero]
    _ = - (1/√2) := by
      rw [inner_ket0_ket1, inner_ket1_ket1, mul_zero, one_div_mul_eq_div, sub_eq_neg_self]

/-- ⟨1|-⟩ = - 1/√2 -/
lemma inner_ket1_ketM : @inner 𝕜 𝕜² _ ket1 ketM = - (1/√2) := by
  calc
    @inner 𝕜 𝕜² _ ket1 ketM
      = @inner 𝕜 𝕜² _ ket1 ((1/√2 : 𝕜) • (ket0 - ket1))                                 := rfl
    _ = @inner 𝕜 𝕜² _ ket1 (((1/√2 : 𝕜) • ket0) - ((1/√2 : 𝕜) • ket1))                  := by
      refine Inseparable.inner_eq_inner rfl ?_; refine Inseparable.of_eq ?_
      rw [smul_sub]
    _ = @inner 𝕜 𝕜² _ ket1 ((1/√2 : 𝕜) • ket0) - @inner 𝕜 𝕜² _ ket1 ((1/√2 : 𝕜) • ket1) := by
      rw [inner_sub_right]
    _ = (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket0 - (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ket1 ket1    := by
      repeat rw [inner_smul_right]
    _ = - (1/√2) := by
      rw [inner_ket1_ket0, inner_ket1_ket1, mul_zero, zero_sub, mul_one]

lemma inner_ketM_ketP : @inner 𝕜 𝕜² _ ketM ketP = 0 := by
  calc
    @inner 𝕜 𝕜² _ ketM ketP
      = @inner 𝕜 𝕜² _ ((1/√2 : 𝕜) • (ket0 - ket1)) ((1/√2 : 𝕜) • (ket0 + ket1)) := rfl
    _ = starRingEnd 𝕜 (1/√2 : 𝕜) * (1/√2 : 𝕜) * @inner 𝕜 𝕜² _ ((ket0 - ket1)) ((ket0 + ket1)) := by rw [inner_smul_left, inner_smul_right, mul_assoc]
    _ = (1/2) * @inner 𝕜 𝕜² _ (ket0 - ket1) (ket0 + ket1) := by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]
    _ = (1/2) * (@inner 𝕜 𝕜² _ ket0 (ket0 + ket1) - @inner 𝕜 𝕜² _ ket1 (ket0 + ket1)) := by rw [inner_sub_left]
    _ = (1/2) * (@inner 𝕜 𝕜² _ ket0 ket0 + @inner 𝕜 𝕜² _ ket0 ket1 - (@inner 𝕜 𝕜² _ ket1 ket0 + @inner 𝕜 𝕜² _ ket1 ket1)) := by repeat rw [inner_add_right]
    _ = (1/2) * (1 + 0 - (0 + 1)) := by rw [inner_ket0_ket0, inner_ket0_ket1, inner_ket1_ket0, inner_ket1_ket1]
    _ = 0 := by ring

lemma inner_ketP_ketM : @inner 𝕜 𝕜² _ ketP ketM = 0 :=
  inner_eq_zero_symm.mp inner_ketM_ketP

lemma ket0_eq_ketP_add_ketM : (ket0 : 𝕜²) = (1/√2 : 𝕜) • (ketP + ketM) := by
  unfold ketM ketP
  rw [← smul_add, add_add_sub_cancel, smul_smul,
    show (1/√2 : 𝕜) * (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat],
    smul_add, ← add_smul, add_halves, one_smul]

lemma ket1_eq_ketP_sub_ketM : (ket1 : 𝕜²) = (1/√2 : 𝕜) • (ketP - ketM) := by
  unfold ketM ketP
  rw [← smul_sub, add_sub_sub_cancel, smul_smul,
    show (1/√2 : 𝕜) * (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat],
    smul_add, ← add_smul, add_halves, one_smul]

/-- |0⟩⟨0| + |1⟩⟨1| = I -/
lemma ketbra0_add_ketbra1_eq_one :
  ketbra0 + ketbra1 = (1 : 𝕜² →ₗ[𝕜] 𝕜²) := by
  unfold ketbra0 ketbra1
  refine LinearMap.ext_iff.mpr ?_
  simp only [LinearMap.add_apply, Module.End.one_apply]
  intro x
  repeat rw [outerProduct_assoc_right]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, Fin.isValue]
  unfold ket0 ket1
  simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, map_one, mul_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, map_zero, mul_zero, add_zero, zero_add]
  ext i
  simp
  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, mul_one, mul_zero, add_zero]
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, mul_one, zero_add]

lemma ketbra0_eq : ketbra0 = (1/2 : 𝕜) • ketbraP + (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM :=
  calc
    ketbra0
      = outerProduct 𝕜 ket0 ket0 := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ketP + ketM)) ket0 := by nth_rw 1 [ket0_eq_ketP_add_ketM]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ketP + ketM) ket0 := by apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ketP ket0 + outerProduct 𝕜 ketM ket0) := by
      rw [RCLike.ofReal_alg, outerProduct_add_dist_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ket0 + (1/√2 : 𝕜) • outerProduct 𝕜 ketM ket0 := by
      rw [smul_add]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ((1/√2 : 𝕜) • (ketP + ketM)) + (1/√2 : 𝕜) • outerProduct 𝕜 ketM ((1/√2 : 𝕜) • (ketP + ketM)) := by
      repeat rw [ket0_eq_ketP_add_ketM]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketP (ketP + ketM) + (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketM (ketP + ketM) := by
      rw [← smul_add]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, smul_add]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ketP (ketP + ketM) + (1/2 : 𝕜) • outerProduct 𝕜 ketM (ketP + ketM) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbraP + (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM := by
      repeat rw [outerProduct_add_dist_right]
      simp only [smul_add]
      rw [← ketbraM, ← ketMbraP, ← ketPbraM, ← ketbraP]
      abel

lemma ketbra1_eq : ketbra1 = (1/2 : 𝕜) • ketbraP - (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM :=
  calc
    ketbra1
      = outerProduct 𝕜 ket1 ket1 := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ketP - ketM)) ket1 := by nth_rw 1 [ket1_eq_ketP_sub_ketM]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ketP - ketM) ket1 := by apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ketP ket1 - outerProduct 𝕜 ketM ket1) := by
      rw [RCLike.ofReal_alg, outerProduct_sub_dist_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ket1 - (1/√2 : 𝕜) • outerProduct 𝕜 ketM ket1 := by
      rw [smul_sub]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ketP ((1/√2 : 𝕜) • (ketP - ketM)) - (1/√2 : 𝕜) • outerProduct 𝕜 ketM ((1/√2 : 𝕜) • (ketP - ketM)) := by
      repeat rw [ket1_eq_ketP_sub_ketM]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketP (ketP - ketM) - (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ketM (ketP - ketM) := by
      rw [← smul_sub]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, smul_sub]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ketP (ketP - ketM) - (1/2 : 𝕜) • outerProduct 𝕜 ketM (ketP - ketM) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbraP - (1/2 : 𝕜) • (ketPbraM : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) •  ketMbraP + (1/2 : 𝕜) • ketbraM := by
      repeat rw [outerProduct_sub_dist_right]
      simp only [smul_sub]
      rw [← ketbraM, ← ketMbraP, ← ketPbraM, ← ketbraP]
      abel

/-- |+⟩⟨+| = 1/2 • (|0⟩⟨0| + |0⟩⟨1| + |1⟩⟨0| + |1⟩⟨1|) -/
lemma ketbraP_eq : ketbraP = (1/2 : 𝕜) • ketbra0 + (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ket1bra0 + (1/2 : 𝕜) • ketbra1 :=
  calc
    ketbraP
      = outerProduct 𝕜 ketP ketP := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ket0 + ket1)) ketP  := by nth_rw 1 [ketP]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ket0 + ket1) ketP    := by apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ket0 ketP + outerProduct 𝕜 ket1 ketP) := by
      rw [RCLike.ofReal_alg, outerProduct_add_dist_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ketP + (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ketP := by
      rw [smul_add]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ((1/√2 : 𝕜) • (ket0 + ket1)) + (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ((1/√2 : 𝕜) • (ket0 + ket1)) := by
      repeat rw [ketP]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 + ket1) + (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 + ket1) := by
      rw [← smul_add]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal, smul_add]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 + ket1) + (1/2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 + ket1) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbra0 + (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) + (1/2 : 𝕜) •  ket1bra0 + (1/2 : 𝕜) • ketbra1 := by
      repeat rw [outerProduct_add_dist_right]
      simp only [smul_add]
      rw [← ketbra0, ← ket1bra0, ← ket0bra1, ← ketbra1]
      abel

/-- |-⟩⟨-| = 1/2 • (|0⟩⟨0| - |0⟩⟨1| - |1⟩⟨0| + |1⟩⟨1|) -/
lemma ketbraM_eq : ketbraM = (1/2 : 𝕜) • ketbra0 - (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) • ket1bra0 + (1/2 : 𝕜) • ketbra1 :=
  calc
    ketbraM
      = outerProduct 𝕜 ketM ketM                          := rfl
    _ = outerProduct 𝕜 ((1/√2 : 𝕜) • (ket0 - ket1)) ketM  := by nth_rw 1 [ketM]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 (ket0 - ket1) ketM    := by
      apply outerProduct_smul_assoc_left
    _ = (1/√2 : 𝕜) • (outerProduct 𝕜 ket0 ketM - outerProduct 𝕜 ket1 ketM) := by
      rw [RCLike.ofReal_alg, outerProduct_sub_dist_left]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ketM - (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ketM := by
      rw [smul_sub]
    _ = (1/√2 : 𝕜) • outerProduct 𝕜 ket0 ((1/√2 : 𝕜) • (ket0 - ket1)) - (1/√2 : 𝕜) • outerProduct 𝕜 ket1 ((1/√2 : 𝕜) • (ket0 - ket1)) := by
      repeat rw [ketM]
    _ = (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 - ket1) - (1/√2 : 𝕜) • (1/√2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 - ket1) := by
      rw [← smul_sub]
      repeat rw [outerProduct_smul_assoc_right]
      simp only [one_div, map_inv₀, RCLike.conj_ofReal]
      rw [smul_sub]
    _ = (1/2 : 𝕜) • outerProduct 𝕜 ket0 (ket0 - ket1) - (1/2 : 𝕜) • outerProduct 𝕜 ket1 (ket0 - ket1) := by
      repeat rw [← smul_assoc, show (1/√2 : 𝕜) • (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
    _ = (1/2 : 𝕜) • ketbra0 - (1/2 : 𝕜) • (ket0bra1 : 𝕜² →ₗ[𝕜] 𝕜²) - (1/2 : 𝕜) •  ket1bra0 + (1/2 : 𝕜) • ketbra1 := by
      repeat rw [outerProduct_sub_dist_right]
      simp only [smul_sub]
      rw [← ketbra0, ← ket1bra0, ← ket0bra1, ← ketbra1]
      abel

/-- |+⟩⟨+| = I - |-⟩⟨-| -/
lemma ketbraP_eq_one_sub_ketbraM :
  ketbraP = (1 : 𝕜² →ₗ[𝕜] 𝕜²) - ketbraM := by
    rw [eq_sub_iff_add_eq]
    rw [ketbraP_eq, ketbraM_eq]
    simp only [smul_add]
    abel_nf
    repeat rw [← smul_assoc]
    repeat rw [one_div]
    simp only [zsmul_eq_mul, Int.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, IsUnit.mul_inv_cancel, one_smul]
    apply ketbra0_add_ketbra1_eq_one

/-- |+⟩⟨+| + |-⟩⟨-| = I -/
lemma ketbraP_add_ketbraM_eq_one :
  ketbraP + ketbraM = (1 : 𝕜² →ₗ[𝕜] 𝕜²)  := by
    rw [← @eq_sub_iff_add_eq]
    apply ketbraP_eq_one_sub_ketbraM

lemma ketbraP_ket0_eq_smul_ketP : (ketbraP ket0 : 𝕜²) = (1 / √2 : 𝕜) • ketP := by
  unfold ketbraP
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ketP_ket0]

lemma ketbraP_ket1_eq_smul_ketP : (ketbraP ket1 : 𝕜²) = (1 / √2 : 𝕜) • ketP := by
  unfold ketbraP
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ketP_ket1]

lemma ketbra0_ketP_eq_smul_ket0 : (ketbra0 ketP : 𝕜²) = (1 / √2 : 𝕜) • ket0 := by
  unfold ketbra0
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ket0_ketP]

lemma ketbra1_ketP_eq_smul_ket1 : (ketbra1 ketP : 𝕜²) = (1 / √2 : 𝕜) • ket1 := by
  unfold ketbra1
  unfold outerProduct
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_ket1_ketP]

lemma hadamard_ketP_eq_ket0 : Hadamard ketP = (ket0 : 𝕜²) := by
  unfold Hadamard
  rw [LinearMap.add_apply, outerProduct_def, outerProduct_def, inner_ketP_ketP, inner_ketM_ketP]
  simp

lemma adjoint_Hadamard_eq : Hadamard.adjoint = outerProduct 𝕜 ketP ket0 + outerProduct 𝕜 ketM ket1 := by
  unfold Hadamard
  simp [adjoint_outerProduct]

lemma adjoint_Hadamard_mul_ketbraP_mul_Hadamard_eq_ketbra0 :
    Hadamard.adjoint * (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²) * Hadamard = ketbra0 := by
  rw [adjoint_Hadamard_eq, Hadamard]
  unfold ketbraP
  rw [left_distrib]
  repeat rw [right_distrib]
  repeat rw [outerProduct_mul_outerProduct_eq_inner_smul_outerProduct]
  repeat rw [smul_mul_assoc]
  repeat rw [outerProduct_mul_outerProduct_eq_inner_smul_outerProduct]
  repeat rw [inner_ketP_ket0, inner_ket0_ketP, inner_ketP_ket1, inner_ket1_ketP]
  repeat rw [smul_smul]
  repeat rw [show (1/√2 : 𝕜) * (1/√2 : 𝕜) = 1 / 2 by field_simp [← RCLike.ofReal_mul, RCLike.ofReal_ofNat]]
  rw [← ketbraP, ← ketMbraP, ← ketPbraM, ← ketbraM, ketbra0_eq]
  abel

lemma span_ketP_eq_span_ketM_comp : (𝕜 ∙ ketP : Submodule 𝕜 𝕜²) = (𝕜 ∙ ketM)ᗮ :=
  Submodule.span_singleton_eq_orthogonal_of_inner_eq_zero finrank_euclideanSpace_fin
  (neZero_iff.mp neZero_ketP) (neZero_iff.mp neZero_ketM) inner_ketP_ketM

lemma span_ketM_eq_span_ketP_comp : (𝕜 ∙ ketM : Submodule 𝕜 𝕜²) = (𝕜 ∙ ketP)ᗮ :=
  Submodule.span_singleton_eq_orthogonal_of_inner_eq_zero finrank_euclideanSpace_fin
  (neZero_iff.mp neZero_ketM) (neZero_iff.mp neZero_ketP) inner_ketM_ketP

def stBasis_val : Fin 2 → 𝕜²
  | 0 => ket0
  | 1 => ket1

lemma Orthonormal_stBasis_val : Orthonormal 𝕜 (E := 𝕜²) stBasis_val := by
  apply And.intro
  · intro i
    fin_cases i
    · exact norm_ket0
    · exact norm_ket1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
    · simp only [stBasis_val, Fin.sum_univ_two, Fin.isValue]
      exact inner_ket0_ket1
    · simp only [stBasis_val, Fin.sum_univ_two, Fin.isValue]
      exact inner_ket1_ket0

noncomputable def stBasis : Basis (Fin 2) 𝕜 𝕜² :=
  basisOfOrthonormalOfCardEqFinrank Orthonormal_stBasis_val finrank_euclideanSpace_fin.symm

lemma stBasis_eq_stBasis_val : (stBasis : Fin 2 → 𝕜²) = stBasis_val := by
  apply funext_iff.mpr
  intro i
  simp [stBasis]

lemma Orthonormal_stBasis : Orthonormal 𝕜 (E := 𝕜²) stBasis := by
  rw [stBasis_eq_stBasis_val]
  exact Orthonormal_stBasis_val

noncomputable def stOrthonormalBasis : OrthonormalBasis (Fin 2) 𝕜 𝕜² :=
  stBasis.toOrthonormalBasis (E := 𝕜²) Orthonormal_stBasis

lemma stOrthonormalBasis_eq_stBasis_val :
    (stOrthonormalBasis (𝕜 := 𝕜) : Fin 2 → 𝕜²) = stBasis_val := by
  simp only [stOrthonormalBasis, Basis.coe_toOrthonormalBasis]
  exact stBasis_eq_stBasis_val
