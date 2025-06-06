/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import LeanVeri.TensorProduct
import Mathlib.LinearAlgebra.Trace

/-!
This file defines the partial trace.
-/

namespace TensorProduct

variable (𝕜 E F : Type*) [RCLike 𝕜]

variable [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]


noncomputable def tr1_aux1 : (E →ₗ[𝕜] E) →ₗ[𝕜] (F →ₗ[𝕜] F) →ₗ[𝕜] F →ₗ[𝕜] F :=
  LinearMap.lsmul 𝕜 (F →ₗ[𝕜] F) ∘ₗ LinearMap.trace 𝕜 E

noncomputable def tr1_aux2 : (E →ₗ[𝕜] E) ⊗[𝕜] (F →ₗ[𝕜] F) →ₗ[𝕜] F →ₗ[𝕜] F :=
  lift (tr1_aux1 𝕜 E F)

noncomputable def tr1 : ((E ⊗[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] F)) →ₗ[𝕜] F →ₗ[𝕜] F :=
  tr1_aux2 𝕜 E F ∘ₗ tprod_map_map_equiv_map_tprod_map 𝕜 E E F F

noncomputable def tr2 : ((E ⊗[𝕜] F) →ₗ[𝕜] (E ⊗[𝕜] F)) →ₗ[𝕜] E →ₗ[𝕜] E :=
  tr1 𝕜 F E ∘ₗ LinearEquiv.arrowCongr (TensorProduct.comm 𝕜 E F) (TensorProduct.comm 𝕜 E F)

end TensorProduct

