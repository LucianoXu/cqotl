import LeanVeri.CommonsTensor
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule
import LeanVeri.TensorProduct

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

open scoped TensorProduct

lemma obligation1 :
    LinearMap.LoewnerOrder (𝕜 := 𝕜) ketbra11 (ket10bra01 + ket01bra10 + ketbra11 + ketbra00) := sorry

def X : 𝕜² →ₗ[𝕜] 𝕜² := sorry

lemma obligation2 :
    LinearMap.LoewnerOrder
      ketbra10
      (TensorProduct.map_tprod_map_equiv_tprod_map_tprod 𝕜 𝕜² 𝕜² 𝕜² 𝕜² (LinearMap.adjoint X ⊗ₜ[𝕜] 1)
        ∘ₗ ketbra11
        ∘ₗ TensorProduct.map_tprod_map_equiv_tprod_map_tprod 𝕜 𝕜² 𝕜² 𝕜² 𝕜² (X ⊗ₜ[𝕜] 1)
      ) := sorry

lemma obligation3 :
    LinearMap.LoewnerOrder
      (LinearMap.SubmoduleInf
        (TensorProduct.map_tprod_map_equiv_tprod_map_tprod 𝕜 𝕜² 𝕜² 𝕜² 𝕜² (ketbra1 ⊗ₜ[𝕜] 1))
        (TensorProduct.map_tprod_map_equiv_tprod_map_tprod 𝕜 𝕜² 𝕜² 𝕜² 𝕜² (1 ⊗ₜ[𝕜] ketbra0)))
      ketbra10 := sorry

lemma obligation4 :
    LinearMap.LoewnerOrder (𝕜 := 𝕜)
      ketbra0
      (LinearMap.adjoint Hadamard ∘ₗ ketbraP ∘ₗ Hadamard) := sorry
