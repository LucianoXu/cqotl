/-
Copyright (c) 2025 Iván Renison, Jam Khan. All rights reserved.
Authors: Iván Renison, Jam Khan
-/
import LeanVeri.LinearMapPropositions
import LeanVeri.OuterProduct
import Mathlib

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

/-- Ket zero times bra zero, usually denoted as |0⟩⟨0|. -/
def ketbra0 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket0 ket0

/-- Ket one times bra one, usually denoted as |1⟩⟨1|. -/
def ketbra1 : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ket1 ket1

/-- Ket plus times bra plus, usually denoted as |+⟩⟨+|. -/
noncomputable def ketbraP : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketP ketP

/-- Ket minus times bra minus, usually denoted as |-⟩⟨-|. -/
noncomputable def ketbraM : 𝕜² →ₗ[𝕜] 𝕜² :=
  outerProduct 𝕜 ketM ketM

lemma ketP_eq : ketP = !₂[1/√2, 1/√2] := by
  unfold ketP ket0 ket1
  simp [← WithLp.equiv_symm_add, ← WithLp.equiv_symm_smul]

lemma ketM_eq : ketM = !₂[1/√2, -1/√2] := by
  unfold ketM ket0 ket1
  simp only [← WithLp.equiv_symm_sub, ← WithLp.equiv_symm_smul]
  field_simp

lemma norm_ket0 : @norm 𝕜² _ ket0 = 1 := by
  unfold norm PiLp.instNorm
  simp [ket0]

lemma norm_ket1 : @norm 𝕜² _ ket1 = 1 := by
  unfold norm PiLp.instNorm
  simp [ket1]

lemma norm_ketP : @norm 𝕜² _ ketP = 1 := by
  unfold norm PiLp.instNorm
  field_simp [ketP, ket0, ket1]

lemma norm_ketM : @norm 𝕜² _ ketM = 1 := by
  unfold norm PiLp.instNorm
  field_simp [ketM, ket0, ket1]

lemma isSelfAdjoint_ketbra0 : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbra0 :=
  IsSelfAdjoint_outerProduct_self 𝕜 ket0

lemma isSelfAdjoint_ketbra1 : @IsSelfAdjoint (𝕜² →ₗ[𝕜] 𝕜²) _ ketbra1 :=
  IsSelfAdjoint_outerProduct_self 𝕜 ket1

lemma isProjection_ketbraP : @LinearMap.isProjection 𝕜 𝕜² _ _ _ _ ketbraP :=
  isProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ketP

lemma isProjection_ketbraM : @LinearMap.isProjection 𝕜 𝕜² _ _ _ _ ketbraM :=
  isProjection_outerProduct_self_of_norm_eq_one 𝕜 norm_ketM

