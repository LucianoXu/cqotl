import LeanVeri.Commons
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

def μ  : Bool → 𝕜
  | _ => 1/2

def P1 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra1

lemma obligation (ρ : 𝕜² →ₗ[𝕜] 𝕜²) (h1 : (LinearMap.isDensityOperator ρ)) (h2 : ((LinearMap.toSubmodule ρ) ≤ (LinearMap.toSubmodule 0))) :
    ((((LinearMap.trace 𝕜) 𝕜²) (P1 * ρ)) = (μ true)) := by
  rw [LinearMap.toSubmodule_zero] at h2
  have h2' : ρ = 0 := LinearMap.eq_zero_of_toSubmodule_le_bot ρ h2
  rw [h2'] at h1
  unfold LinearMap.isDensityOperator at h1
  have h1' := h1.right
  rw [LinearMap.map_zero (LinearMap.trace 𝕜 𝕜²)] at h1'
  simp at h1'
