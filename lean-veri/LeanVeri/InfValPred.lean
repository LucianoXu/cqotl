/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule

structure InfValPred (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] where
  P : E →ₗ[𝕜] E
  X : E →ₗ[𝕜] E
  PisPos : P.isPositiveSemiDefinite
  XisProj : X.isProjection
  compPX : X ∘ₗ P = 0

namespace InfValPred

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

lemma eq_iff (A B : InfValPred 𝕜 E) : A = B ↔ A.P = B.P ∧ A.X = B.X := by
  apply Iff.intro
  · intro h
    rw [h]
    exact And.intro rfl rfl
  · intro ⟨hP, hX⟩
    cases A
    cases B
    congr

noncomputable instance Add : Add (InfValPred 𝕜 E) where
  add A B :=
    let X := A.X.SubmoduleSup B.X
    let Xc := X.SubmoduleComplement
    let P := Xc ∘ₗ (A.P + B.P) ∘ₗ Xc
    have hX : X.isProjection := by apply Submodule.toProjection_valid
    have hXc : Xc.isProjection := by apply Submodule.toProjection_valid
    have haPbP : (A.P + B.P).isPositiveSemiDefinite :=
      LinearMap.isPositiveSemiDefinite_add_of_isPositiveSemiDefinite A.PisPos B.PisPos
    {
      P := P
      X := X
      PisPos := by
        apply And.intro
        · apply P.isSymmetric_iff_isSelfAdjoint.mp
          unfold LinearMap.IsSymmetric
          intro x y
          unfold P
          simp only [LinearMap.coe_comp, Function.comp_apply]
          rw [hXc.left.IsSymmetric, haPbP.IsSymmetric, hXc.left.IsSymmetric]
        · intro x
          unfold P
          simp only [LinearMap.coe_comp, Function.comp_apply]
          rw [hXc.left.IsSymmetric]
          exact haPbP.right (Xc x)
      XisProj := by apply Submodule.toProjection_valid
      compPX := by
        unfold P Xc
        rw [← LinearMap.comp_assoc, hX.comp_Complement]
        rfl
    }

lemma add_X_def (A B : InfValPred 𝕜 E) :
    (A + B).X = A.X.SubmoduleSup B.X := rfl

lemma add_P_def (A B : InfValPred 𝕜 E) :
    (A + B).P = (A.X.SubmoduleSup B.X).SubmoduleComplement ∘ₗ (A.P + B.P) ∘ₗ (A.X.SubmoduleSup B.X).SubmoduleComplement := rfl

noncomputable instance AddCommMagma : AddCommMagma (InfValPred 𝕜 E) where
  add_comm A B := by
    apply (eq_iff _ _).mpr
    apply And.intro
    · simp [add_P_def, LinearMap.SubmoduleSup_comm, add_comm]
    · simp [add_X_def, LinearMap.SubmoduleSup_comm]

open scoped ENNReal

noncomputable instance HSMul : HSMul ℝ≥0∞ (InfValPred 𝕜 E) (InfValPred 𝕜 E) where
  hSMul c A :=
    match c with
      | ∞ =>
        {
          P := 0
          X := 1
          PisPos := LinearMap.isPositiveSemiDefinite.zero
          XisProj := LinearMap.isProjection.one
          compPX := rfl
        }
      | some c =>
        {
          P := (c.val : 𝕜) • A.P
          X := A.X
          PisPos := A.PisPos.isPositiveSemiDefinite_nonneg_real_smul c c.zero_le_coe
          XisProj := A.XisProj
          compPX := by
            rw [LinearMap.comp_smul]
            exact smul_eq_zero.mpr (Or.inr A.compPX)
        }

end InfValPred
