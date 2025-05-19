/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Data.ENNReal.Real
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule

/-!
This file defines infinite value predicates and proves some basic properties about them.
An infinite value predicate is something like a positive semi definite operator, but that also
maps certain subspaces to infinite.
-/

/-- Infinite value predicate. -/
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

/-- Convert a positive semi definite operator in to a infinite value predicate -/
def _root_.isPositiveSemiDefinite.toInfValPred {P : E →ₗ[𝕜] E} (hP : P.isPositiveSemiDefinite) : InfValPred 𝕜 E :=
  {
    P := P
    X := 0
    PisPos := hP
    XisProj := LinearMap.isProjection.zero
    compPX := rfl
  }

instance Zero : Zero (InfValPred 𝕜 E) where
  zero :=
    {
      P := 0
      X := 0
      PisPos := LinearMap.isPositiveSemiDefinite.zero
      XisProj := LinearMap.isProjection.zero
      compPX := rfl
    }

lemma zero_X_def : (0 : InfValPred 𝕜 E).X = 0 := rfl
lemma zero_P_def : (0 : InfValPred 𝕜 E).P = 0 := rfl

instance One : One (InfValPred 𝕜 E) where
  one :=
    {
      P := 1
      X := 0
      PisPos := LinearMap.isPositiveSemiDefinite.one
      XisProj := LinearMap.isProjection.zero
      compPX := rfl
    }

lemma one_X_def : (1 : InfValPred 𝕜 E).X = 0 := rfl
lemma one_P_def : (1 : InfValPred 𝕜 E).P = 1 := rfl

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
          PisPos := A.PisPos.nonneg_real_smul c.zero_le_coe
          XisProj := A.XisProj
          compPX := by
            rw [LinearMap.comp_smul]
            exact smul_eq_zero.mpr (Or.inr A.compPX)
        }

/-- Analog to `inner 𝕜 (T x) x` for positive semi definite operator `T`. -/
def inner_app_self (A : InfValPred 𝕜 E) (x : E) : ℝ≥0∞ :=
  if inner 𝕜 (A.X x) x = 0
    then some ⟨RCLike.re (inner 𝕜 (A.P x) x), A.PisPos.right x⟩
    else ∞

/-- Löwner Order for infinite value predicates. -/
def LoewnerOrder (A B : InfValPred 𝕜 E) : Prop :=
  ∀x : E, A.inner_app_self x ≤ B.inner_app_self x

end InfValPred
