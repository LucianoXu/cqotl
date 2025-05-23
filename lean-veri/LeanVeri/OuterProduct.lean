/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.LinearMapPropositions

/-!
This file defines the outer product of two vectors as a linear map,
and proves basic properties of the outer product.
-/

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The outer product of two vectors -/
def outerProduct (x : E) (y : E) : E →ₗ[𝕜] E where
  toFun := fun z => (inner 𝕜 y z) • x
  map_add' z w := by
    rw [← Module.add_smul, inner_add_right y z w]
  map_smul' m z := by
    rw [RingHom.id_apply, inner_smul_right_eq_smul y z m]
    exact IsScalarTower.smul_assoc m (inner 𝕜 y z) x

omit [FiniteDimensional 𝕜 E] in
lemma outerProduct_def (x : E) (y : E) (z : E) :
    outerProduct 𝕜 x y z = (inner 𝕜 y z) • x := rfl

lemma IsSelfAdjoint_outerProduct_self (x : E) :
    IsSelfAdjoint (outerProduct 𝕜 x x) := by
  rw [← LinearMap.isSymmetric_iff_isSelfAdjoint]
  intro y z
  simp only [outerProduct_def]
  rw [inner_smul_left, inner_smul_right, InnerProductSpace.conj_inner_symm]
  ring

lemma IsSymmetric_outerProduct_self (x : E) : (outerProduct 𝕜 x x).IsSymmetric :=
  (outerProduct 𝕜 x x).isSymmetric_iff_isSelfAdjoint.mpr (IsSelfAdjoint_outerProduct_self 𝕜 x)

lemma isPositiveSemiDefinite_outerProduct_self (x : E) :
    (outerProduct 𝕜 x x).isPositiveSemiDefinite := by
  apply And.intro (IsSelfAdjoint_outerProduct_self 𝕜 x)
  intro y
  simp only [outerProduct_def]
  rw [inner_smul_left, InnerProductSpace.conj_inner_symm, inner_mul_symm_re_eq_norm]
  exact norm_nonneg (inner 𝕜 y x * inner 𝕜 x y)

lemma isProjection_outerProduct_self_of_norm_eq_one {x : E} (h : ‖x‖ = 1) :
    (outerProduct 𝕜 x x).isProjection := by
  apply And.intro (isPositiveSemiDefinite_outerProduct_self 𝕜 x)
  rw [LinearMap.ext_iff]
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, outerProduct_def]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, h]
  simp
