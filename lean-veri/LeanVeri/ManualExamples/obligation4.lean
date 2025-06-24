import LeanVeri.CommonsTensor
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule
import LeanVeri.TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)

open scoped TensorProduct

lemma obligation1 :
    LinearMap.LoewnerOrder (𝕜 := 𝕜) ketbra11 (ket10bra01 + ket01bra10 + ketbra11 + ketbra00) := by
  sorry

def X : 𝕜² →ₗ[𝕜] 𝕜² := sorry

lemma obligation2 :
    LinearMap.LoewnerOrder
      ketbra10
      (TensorProduct.tmul_cast 𝕜 𝕜² 𝕜² 𝕜² 𝕜² (LinearMap.adjoint X) 1
        ∘ₗ ketbra11
        ∘ₗ TensorProduct.tmul_cast 𝕜 𝕜² 𝕜² 𝕜² 𝕜² X 1
      ) := sorry

lemma obligation3 :
    LinearMap.LoewnerOrder
      (LinearMap.SubmoduleInf
        (TensorProduct.tmul_cast 𝕜 𝕜² 𝕜² 𝕜² 𝕜² ketbra1 1)
        (TensorProduct.tmul_cast 𝕜 𝕜² 𝕜² 𝕜² 𝕜² 1 ketbra0))
      ketbra10 := sorry

lemma obligation4 :
    LinearMap.LoewnerOrder (𝕜 := 𝕜)
      ketbra0
      (LinearMap.adjoint Hadamard ∘ₗ ketbraP ∘ₗ Hadamard) := sorry
