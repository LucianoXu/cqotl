import LeanVeri.Commons
import LeanVeri.LinearMapPropositions

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

noncomputable def H : 𝕜² →ₗ[𝕜] 𝕜² := Hadamard

noncomputable def ketPlus : 𝕜² := ketP

def ket0bra0 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra0

def ket1bra1 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra1

lemma obligation1 :
   ((LinearMap.LoewnerOrder ket0bra0) ((Hadamard.adjoint * (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²)) * Hadamard)) := by
  rw [adjoint_Hadamard_mul_ketbraP_mul_Hadamard_eq_ketbra0, ket0bra0]
  exact LinearMap.reflexive_LoewnerOrder (𝕜 := 𝕜) ket0bra0
