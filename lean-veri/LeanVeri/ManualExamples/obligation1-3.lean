import LeanVeri.Commons
import LeanVeri.LinearMapPropositions

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

noncomputable def H : 𝕜² →ₗ[𝕜] 𝕜² := Hadamard

noncomputable def ketPlus : 𝕜² := ketP

def ket0bra0 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra0

def ket1bra1 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra1

lemma obligation :
    ((LinearMap.LoewnerOrder ket0bra0) (((outerProduct 𝕜) (H ketPlus)) (H ketPlus))) := by
  simp only [ket1bra1, ket0bra0, ketPlus, H]
  rw [hadamard_ketP_eq_ket0]
  rw [← ketbra0]
  exact LinearMap.reflexive_LoewnerOrder (𝕜 := 𝕜) ketbra0
