/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.LinearMapPropositions
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
There is a one to one correspondence between the projection operators and the subspaces.
Note that we use the name `Submodule` for the subspaces, as in `Mathlib`.
In this file we define this correspondence and prove some basic properties about it.
-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The `Submodule` corresponding to a projection. This definition works for any `LinearMap`, but only makes sense for
projections. -/
def LinearMap.toSubmodule (T : E →ₗ[𝕜] E) : Submodule 𝕜 E := (LinearMap.ker T)ᗮ

/-- The projection corresponding to a `Submodule` as a `LinearMap` -/
noncomputable def Submodule.toProjection (K : Submodule 𝕜 E) : E →ₗ[𝕜] E :=
  K.subtype ∘ₗ K.orthogonalProjection

lemma Submodule.toProjection_eq (K : Submodule 𝕜 E) (x : E) :
    K.toProjection x = K.orthogonalProjection x := rfl

lemma Submodule.toProjection_valid (K : Submodule 𝕜 E) :
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

lemma Submodule.toSubmodule_toProjection_eq (K : Submodule 𝕜 E) :
    K.toProjection.toSubmodule = K := by
  unfold toProjection
  unfold LinearMap.toSubmodule
  rw [← orthogonalComplement_eq_orthogonalComplement, orthogonal_orthogonal, Submodule.ext_iff]
  intro x
  rw [LinearMap.mem_ker, ← orthogonalProjection_eq_zero_iff]
  simp

lemma LinearMap.isProjection.toSubmodule_eq_range {T : E →ₗ[𝕜] E} (hT : T.isProjection) :
    T.toSubmodule = range T := by
  rw [eq_comm]
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    unfold toSubmodule
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← hT.apply_range hx, ← (isSymmetric_iff_isSelfAdjoint T).mpr hT.left.left, hu]
    exact inner_zero_left x
  · unfold toSubmodule
    rw [Nat.eq_sub_of_add_eq' (ker T).finrank_add_finrank_orthogonal, eq_tsub_iff_add_eq_of_le (ker T).finrank_le]
    exact finrank_range_add_finrank_ker T

lemma LinearMap.isProjection.toProjection_toSubmodule_eq {T : E →ₗ[𝕜] E} (hT : T.isProjection) :
    T.toSubmodule.toProjection = T := by
  rw [LinearMap.ext_iff]
  intro x
  have hx := Submodule.exists_add_mem_mem_orthogonal (ker T) x
  obtain ⟨y, hy, z, hz, hxyz⟩ := hx
  rw [hxyz]
  rw [LinearMap.map_add, LinearMap.map_add]
  apply Mathlib.Tactic.LinearCombination.add_eq_eq
  · rw [Submodule.toProjection_eq]
    unfold LinearMap.toSubmodule
    rw [Submodule.orthogonalProjection_orthogonal_val, Submodule.orthogonalProjection_eq_self_iff.mpr hy, sub_self, hy]
  · rw [Submodule.toProjection_eq]
    unfold LinearMap.toSubmodule
    rw [Submodule.orthogonalProjection_orthogonal_val, Submodule.orthogonalProjection_eq_zero_iff.mpr hz,
      ZeroMemClass.coe_zero, sub_zero]
    have hz' : z ∈ range T := by
      rw [← hT.toSubmodule_eq_range]
      exact hz
    exact (hT.apply_range hz').symm

/-- The projection corresponding to the orthogonal complement of the submodule of the given linear map. -/
noncomputable def LinearMap.SubmoduleComplement (T : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (T.toSubmoduleᗮ).toProjection

/-- The projection corresponding to the intersection of the submodules of the given linear maps. -/
noncomputable def LinearMap.SubmoduleInf (T N : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (T.toSubmodule ⊓ N.toSubmodule).toProjection

/-- The projection corresponding to the sum of the submodules of the given linear maps. -/
noncomputable def LinearMap.SubmoduleSup (T N : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (T.toSubmodule ⊔ N.toSubmodule).toProjection

lemma LinearMap.isProjection.SubmoduleComplement_eq {T : E →ₗ[𝕜] E} (hT : T.isProjection) : T.SubmoduleComplement = 1 - T := by
  rw [LinearMap.ext_iff]
  intro x
  unfold SubmoduleComplement
  rw [Submodule.toProjection_eq, Submodule.orthogonalProjection_orthogonal_val, ← Submodule.toProjection_eq,
    hT.toProjection_toSubmodule_eq]
  rfl

lemma LinearMap.isProjection.comp_Complement {T : E →ₗ[𝕜] E} (hT : T.isProjection) : T ∘ₗ T.SubmoduleComplement = 0 := by
  rw [hT.SubmoduleComplement_eq, comp_sub, Module.End.one_eq_id, comp_id, hT.right]
  exact sub_self T

lemma LinearMap.SubmoduleInf_comm (T N : E →ₗ[𝕜] E) : T.SubmoduleInf N = N.SubmoduleInf T := by
  unfold SubmoduleInf
  rw [inf_comm]

lemma LinearMap.SubmoduleSup_comm (T N : E →ₗ[𝕜] E) : T.SubmoduleSup N = N.SubmoduleSup T := by
  unfold SubmoduleSup
  rw [sup_comm]

lemma LinearMap.SubmoduleInf_assoc (T N M : E →ₗ[𝕜] E) :
    (T.SubmoduleInf N).SubmoduleInf M = T.SubmoduleInf (N.SubmoduleInf M) := by
  unfold SubmoduleInf
  rw [Submodule.toSubmodule_toProjection_eq, Submodule.toSubmodule_toProjection_eq, inf_assoc]

lemma LinearMap.SubmoduleSup_assoc (T N M : E →ₗ[𝕜] E) :
    (T.SubmoduleSup N).SubmoduleSup M = T.SubmoduleSup (N.SubmoduleSup M) := by
  unfold SubmoduleSup
  rw [Submodule.toSubmodule_toProjection_eq, Submodule.toSubmodule_toProjection_eq, sup_assoc]
