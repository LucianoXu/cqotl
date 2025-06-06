/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.TensorProduct.Finite

/-!
This file defines some relation between some tensor product spaces.
-/

namespace TensorProduct

variable (𝕜 E F G H : Type*) [RCLike 𝕜]

variable [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
variable [AddCommGroup G] [Module 𝕜 G] [FiniteDimensional 𝕜 G]
variable [AddCommGroup H] [Module 𝕜 H] [FiniteDimensional 𝕜 H]

omit [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 H] in
lemma finrank_map_tprod_map_eq_finrank_tprod_map_tprod :
    Module.finrank 𝕜 ((E →ₗ[𝕜] F) ⊗[𝕜] (G →ₗ[𝕜] H)) = Module.finrank 𝕜 ((E ⊗[𝕜] G →ₗ[𝕜] F ⊗[𝕜] H)) := by
  simp only [Module.finrank_linearMap, Module.finrank_tensorProduct]
  ring_nf

noncomputable def map_tprod_map_equiv_tprod_map_tprod :
    (E →ₗ[𝕜] F) ⊗[𝕜] (G →ₗ[𝕜] H) ≃ₗ[𝕜] (E ⊗[𝕜] G →ₗ[𝕜] F ⊗[𝕜] H) :=
  LinearEquiv.ofFinrankEq _ _ (finrank_map_tprod_map_eq_finrank_tprod_map_tprod 𝕜 E F G H)

noncomputable def map_tprod_map_map_tprod_map_tprod :
    (E →ₗ[𝕜] F) ⊗[𝕜] (G →ₗ[𝕜] H) →ₗ[𝕜] (E ⊗[𝕜] G →ₗ[𝕜] F ⊗[𝕜] H) :=
  map_tprod_map_equiv_tprod_map_tprod 𝕜 E F G H

noncomputable def tprod_map_map_equiv_map_tprod_map :
    (E ⊗[𝕜] G →ₗ[𝕜] F ⊗[𝕜] H) →ₗ[𝕜] (E →ₗ[𝕜] F) ⊗[𝕜] (G →ₗ[𝕜] H) :=
  (map_tprod_map_equiv_tprod_map_tprod 𝕜 E F G H).symm

end TensorProduct
