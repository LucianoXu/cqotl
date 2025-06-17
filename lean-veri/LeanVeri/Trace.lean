/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
/-!
This file extends the file `Mathlib.Analysis.InnerProductSpace.Trace`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

lemma LinearMap.IsSymmetric.trace_eq_sum_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    T.trace 𝕜 E = ∑i, hT.eigenvalues rfl i := by
  let B := hT.eigenvectorBasis rfl
  rw [T.trace_eq_sum_inner B, RCLike.ofReal_sum]
  apply Fintype.sum_congr
  intro i
  rw [hT.apply_eigenvectorBasis, inner_smul_real_right, inner_self_eq_norm_sq_to_K, B.norm_eq_one]
  simp only [map_one, one_pow, RCLike.ofReal_alg]
