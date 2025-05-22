/-
Copyright (c) 2025 Iván Renison, Jam Khan. All rights reserved.
Authors: Iván Renison, Jam Khan
-/
import LeanVeri.LinearMapPropositions
import LeanVeri.OuterProduct
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.LinearMap.Defs
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

/-- Ket plus equals !₂[1/√2, 1/√2] -/
lemma ketP_eq : ketP = !₂[1/√2, 1/√2] := by
  unfold ketP ket0 ket1
  simp [← WithLp.equiv_symm_add, ← WithLp.equiv_symm_smul]

/-- Ket minus equals !₂[1/√2, -1/√2] -/
lemma ketM_eq : ketM = !₂[1/√2, -1/√2] := by
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

/-- ⟨+|+⟩ = 1 -/
lemma inner_ketP_ketP : @inner 𝕜 𝕜² _ ketP ketP = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ketP norm_ketP).mpr rfl

/-- ⟨-|-⟩ = 1 -/
lemma inner_ketM_ketM : @inner 𝕜 𝕜² _ ketM ketM = 1 :=
  (inner_eq_one_iff_of_norm_one norm_ketM norm_ketM).mpr rfl

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
