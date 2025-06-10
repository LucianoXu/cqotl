import LeanVeri.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

local notation "𝕜n" => EuclideanSpace 𝕜 (Fin n)
local notation "𝕜m" => EuclideanSpace 𝕜 (Fin m)
local notation "𝕜nm" => EuclideanSpace 𝕜 (Fin (n * m))

open scoped TensorProduct

namespace EuclideanSpace
namespace TensorProduct

lemma finrank_tmul_eq_finrank_mul : Module.finrank 𝕜 (𝕜n ⊗[𝕜] 𝕜m) = Module.finrank 𝕜 𝕜nm := by simp

noncomputable def finrank_tmul_equiv_finrank_mul : 𝕜n ⊗[𝕜] 𝕜m ≃ₗ[𝕜] 𝕜nm :=
  LinearEquiv.ofFinrankEq (𝕜n ⊗[𝕜] 𝕜m) 𝕜nm finrank_tmul_eq_finrank_mul

noncomputable instance : Norm (𝕜n ⊗[𝕜] 𝕜m) where
  norm x := norm (finrank_tmul_equiv_finrank_mul x)

@[simp]
lemma norm_eq (x : 𝕜n ⊗[𝕜] 𝕜m) : norm x = norm (finrank_tmul_equiv_finrank_mul x) := rfl

noncomputable instance : SeminormedAddCommGroup (𝕜n ⊗[𝕜] 𝕜m) where
  dist_self x := by simp
  dist_comm x y := by
    simp only [norm_eq, map_sub]
    exact norm_sub_rev _ _
  dist_triangle x y z := by
    simp only [norm_eq, map_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _

noncomputable instance : AddCommGroup (𝕜n ⊗[𝕜] 𝕜m) where

noncomputable instance : PseudoMetricSpace (𝕜n ⊗[𝕜] 𝕜m) where
  dist_self x := by simp
  dist_comm x y := by
    simp only [norm_eq, map_sub]
    exact norm_sub_rev _ _
  dist_triangle x y z := by
    simp only [norm_eq, map_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _

noncomputable instance : MetricSpace (𝕜n ⊗[𝕜] 𝕜m) where
  eq_of_dist_eq_zero := by
    intro x y h
    simp only [dist, norm_eq, map_sub, norm_eq_zero, sub_eq_zero] at h
    exact finrank_tmul_equiv_finrank_mul.injective h

noncomputable instance : NormedAddCommGroup (𝕜n ⊗[𝕜] 𝕜m) where
  dist_eq x y := by simp [dist]

noncomputable instance : NormedSpace 𝕜 (𝕜n ⊗[𝕜] 𝕜m) where
  norm_smul_le x y := by
    simp only [norm_eq, map_smul]
    exact norm_smul_le x _

noncomputable instance : Inner 𝕜 (𝕜n ⊗[𝕜] 𝕜m) where
  inner x y := inner 𝕜 (finrank_tmul_equiv_finrank_mul x) (finrank_tmul_equiv_finrank_mul y)

lemma inner_eq (x y : 𝕜n ⊗[𝕜] 𝕜m) :
    inner 𝕜 x y = inner 𝕜 (finrank_tmul_equiv_finrank_mul x) (finrank_tmul_equiv_finrank_mul y) := rfl

noncomputable instance : InnerProductSpace 𝕜 (𝕜n ⊗[𝕜] 𝕜m) where
  norm_sq_eq_re_inner x := by
    simp only [norm_eq]
    exact norm_sq_eq_re_inner _
  conj_inner_symm x y := by
    simp only [inner_eq]
    exact InnerProductSpace.conj_inner_symm _ _
  add_left x y z := by
    simp only [inner_eq, map_add]
    exact InnerProductSpace.add_left _ _ _
  smul_left x y r := by
    simp only [inner_eq, map_smul]
    exact InnerProductSpace.smul_left _ _ _

end TensorProduct
end EuclideanSpace
