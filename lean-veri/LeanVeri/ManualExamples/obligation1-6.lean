import LeanVeri.Commons
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule
import LeanVeri.OuterProduct

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

def μ  : Bool → 𝕜
  | _ => 1/2

def P0 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra0

noncomputable def vPlus : 𝕜² := ketP

lemma obligation (ρ1 : 𝕜² →ₗ[𝕜] 𝕜²) (h1 : (LinearMap.isDensityOperator ρ1)) (h2 : ((LinearMap.toSubmodule ρ1) ≤ (LinearMap.toSubmodule ketbraP))) :
 ((((LinearMap.trace 𝕜) 𝕜²) (P0 * ρ1)) = (μ false)) := sorry
