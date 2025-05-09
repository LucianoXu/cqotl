/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
This file extends the file `Mathlib.Analysis.InnerProductSpace.Projection`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma Submodule.re_inner_orthogonalProjection_eq_sqNorm (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    RCLike.re (inner 𝕜 (↑(K.orthogonalProjection x)) x) = ‖(↑(K.orthogonalProjection x))‖^2 := by
  rw [re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  rw [div_eq_iff (NeZero.ne' 2).symm]
  rw [pow_two]
  rw [add_sub_assoc]
  rw [eq_sub_iff_add_eq'.symm]
  rw [AddSubgroupClass.coe_norm]
  rw [← mul_sub_one]
  rw [show (2 : ℝ) - 1 = 1 by ring]
  rw [Lean.Grind.CommRing.mul_one]
  rw [← orthogonalProjectionFn_eq]
  rw [sub_eq_iff_eq_add']
  rw [norm_sub_rev]
  exact orthogonalProjectionFn_norm_sq K x

lemma Submodule.re_inner_orthogonalProjection_nonneg (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    0 ≤ RCLike.re (inner 𝕜 (↑(K.orthogonalProjection x)) x) := by
  rw [re_inner_orthogonalProjection_eq_sqNorm K x]
  exact sq_nonneg ‖K.orthogonalProjection x‖
