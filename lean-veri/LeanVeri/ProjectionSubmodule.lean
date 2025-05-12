/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.Projection
import LeanVeri.LinearMapPropositions

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

lemma aux (P Q : E →ₗ[𝕜] E) (u : E) : (u ∈ LinearMap.ker (P + Q)) ↔ (P + Q) u = 0 := by
  exact LinearMap.mem_ker


lemma auxx (P Q : E →ₗ[𝕜] E) (hP : P.isPositiveSemiDefinite) (hQ : Q.isPositiveSemiDefinite) :
    (P + Q).toSubmodule = P.toSubmodule ⊔ Q.toSubmodule := by
  unfold LinearMap.toSubmodule
  rw [Submodule.ext_iff]
  intro x
  apply Iff.intro
  · intro hx
    rw [Submodule.mem_orthogonal'] at hx
    simp [LinearMap.mem_ker] at hx
    rw [Submodule.mem_sup]
    simp [Submodule.mem_orthogonal']
    
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

