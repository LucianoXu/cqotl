/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.Projection
import LeanVeri.LinearMapPropositions
open scoped ComplexOrder

/-!
There is a one to one correspondence between the projection operators and the submodules.
In this file we define this correspondence and prove some basic properties about it.
-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The `Submodule` corresponding to a projection. This definition works for any `LinearMap`, but only makes sense for
projections. -/
def LinearMap.toSubmodule (T : E →ₗ[𝕜] E) : Submodule 𝕜 E := (LinearMap.ker T)ᗮ

/-- The projection corresponding to a `Submodule` as a `LinearMap` -/
noncomputable def Submodule.toProjection (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  K.subtype ∘ₗ K.orthogonalProjection

omit [FiniteDimensional 𝕜 E] in
lemma Submodule.toProjection_eq (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    K.toProjection x = K.orthogonalProjection x := rfl

lemma Submodule.toProjection_valid (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K.toProjection.isProjection := by
  constructor
  · constructor
    · rw [← LinearMap.isSymmetric_iff_isSelfAdjoint]
      unfold LinearMap.IsSymmetric
      intro x y
      unfold toProjection
      simp only [LinearMap.coe_comp]
      exact inner_orthogonalProjection_left_eq_right K x y
    · intro x
      unfold toProjection
      simp only [LinearMap.coe_comp]
      exact re_inner_orthogonalProjection_nonneg K x
  · rw [LinearMap.ext_iff]
    unfold toProjection
    simp

lemma Submodule.toSubmodule_toProjection_eq (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K.toProjection.toSubmodule = K := by
  unfold toProjection
  unfold LinearMap.toSubmodule
  rw [← orthogonalComplement_eq_orthogonalComplement]
  rw [orthogonal_orthogonal]
  rw [Submodule.ext_iff]
  intro x
  rw [LinearMap.mem_ker]
  rw [← orthogonalProjection_eq_zero_iff]
  simp

lemma aux1 (P Q : E →ₗ[𝕜] E) (hP : P.isPositiveSemiDefinite) (hQ : Q.isPositiveSemiDefinite) :
    LinearMap.ker (P + Q) = LinearMap.ker P ⊓ LinearMap.ker Q := by
  have hPQ : (P + Q).isPositiveSemiDefinite := LinearMap.isPositiveSemiDefinite_add_of_isPositiveSemiDefinite hP hQ
  rw [Submodule.ext_iff]
  intro x
  calc
    x ∈ LinearMap.ker (P + Q)
      ↔ (P + Q) x = 0 := rfl.to_iff
    _ ↔ RCLike.re (inner 𝕜 ((P + Q) x) x) = 0 := (hPQ.re_inner_app_eq_zero_iff_app_eq_zero x).symm
    _ ↔ RCLike.re (inner 𝕜 (P x + Q x) x) = 0 := by rw [LinearMap.add_apply]
    _ ↔ RCLike.re (inner 𝕜 (P x) x + inner 𝕜 (Q x) x) = 0 := by rw [inner_add_left]
    _ ↔ RCLike.re (inner 𝕜 (P x) x) + RCLike.re (inner 𝕜 (Q x) x) = 0 := by rw [AddMonoidHom.map_add RCLike.re]
    _ ↔ RCLike.re (inner 𝕜 (P x) x) = 0 ∧ RCLike.re (inner 𝕜 (Q x) x) = 0 := add_eq_zero_iff_of_nonneg (hP.right x) (hQ.right x)
    _ ↔ P x = 0 ∧ Q x = 0 := by rw [hP.re_inner_app_eq_zero_iff_app_eq_zero x, hQ.re_inner_app_eq_zero_iff_app_eq_zero x]
    _ ↔ x ∈ LinearMap.ker P ∧ x ∈ LinearMap.ker Q := rfl.to_iff
    _ ↔ x ∈ LinearMap.ker P ⊓ LinearMap.ker Q := Submodule.mem_inf.symm

lemma ker_union (P Q : E →ₗ[𝕜] E) (hP : LinearMap.isPositiveSemiDefinite P) (hQ : LinearMap.isPositiveSemiDefinite Q):
  (LinearMap.ker P ⊓ LinearMap.ker Q)ᗮ = (LinearMap.ker P)ᗮ ⊔ (LinearMap.ker Q)ᗮ := by
  ext x
  constructor
  · intro H
    
    rw [@Submodule.mem_orthogonal'] at H
    simp_all only [Submodule.mem_inf, LinearMap.mem_ker, and_imp]
    refine Submodule.mem_sup_right ?_
    refine (Submodule.mem_orthogonal' (LinearMap.ker Q) x).mpr ?_
    sorry
  · intro H

    sorry

theorem sup_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊔ K₂ᗮ = (K₁ ⊓ K₂)ᗮ := by

  rw [Submodule.ext_iff]
  intro x
  sorry
/-   calc
    x ∈ K₁ᗮ ⊔ K₂ᗮ
      ↔ ∃

      ↔ x ∈ (K₁ ⊓ K₂)ᗮ := sorry -/
/-   apply Iff.intro
  · intro hx

    sorry
  · sorry -/
  /- apply le_antisymm
  ·
    sorry
  · sorry -/

lemma auxx (P Q : E →ₗ[𝕜] E) (hP : P.isProjection) (hQ : Q.isProjection) :
    (P + Q).toSubmodule = P.toSubmodule ⊔ Q.toSubmodule := by
  unfold LinearMap.toSubmodule
  --rw [Submodule.sup_orthogonal]
  have : (LinearMap.ker P)ᗮ ⊔ (LinearMap.ker Q)ᗮ = (LinearMap.ker P ⊓ LinearMap.ker Q)ᗮ := by
    rw [← Submodule.orthogonalComplement_eq_orthogonalComplement]
    rw [← Submodule.inf_orthogonal]

    --rw [← Submodule.orthogonalComplement_eq_orthogonalComplement]
    sorry
  rw [Submodule.ext_iff]
  intro x
  have hx' := hP.left.inner_app_eq_zero_iff_app_eq_zero x
  apply Iff.intro
  · intro hx
    rw [Submodule.mem_orthogonal'] at hx
    simp [LinearMap.mem_ker] at hx
    rw [Submodule.mem_sup]
    simp [Submodule.mem_orthogonal']
    let y := P x
    let z := Q x
    use y
    apply And.intro
    · intro u hu
      have hu' : inner 𝕜 (P u) u = 0 := (hP.left.inner_app_eq_zero_iff_app_eq_zero u).mpr hu
      unfold y
      sorry
    sorry
  · intro hx
    rw [Submodule.mem_sup] at hx
    rw [Submodule.mem_orthogonal']
    simp [LinearMap.mem_ker]
    intro u hu
    obtain ⟨y, ⟨hy, ⟨z, ⟨hz, hyzx⟩⟩⟩⟩ := hx
    rw [Submodule.mem_orthogonal'] at hy
    simp [LinearMap.mem_ker] at hy
    rw [Submodule.mem_orthogonal'] at hz
    simp [LinearMap.mem_ker] at hz

    sorry

