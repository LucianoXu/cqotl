/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
This file extends the file `Mathlib.Analysis.InnerProductSpace.PiL2`.
-/

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]
variable (b : OrthonormalBasis ι 𝕜 E) (i : ι)

namespace OrthonormalBasis

lemma neZero : NeZero (b i) := by
  rw [neZero_iff]
  have hnorm := b.norm_eq_one i
  intro h
  rw [h] at hnorm
  simp_all

end OrthonormalBasis
