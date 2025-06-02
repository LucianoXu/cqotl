/-
AUTO-GENERATED LEAN4 OBLIGATION BY CQOTL PROVER.
-/
import LeanVeri.Commons
import LeanVeri.LinearMapPropositions

open LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
local notation "𝕜²" => EuclideanSpace 𝕜 (Fin 2)
noncomputable def H : 𝕜² →ₗ[𝕜] 𝕜² := Hadamard
noncomputable def ketPlus : 𝕜² := ketP

def ket1bra1 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra1
def ket0bra0 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra0

lemma obligation1: (LoewnerOrder ketbra0 (outerProduct 𝕜 (H ketPlus) (H ketPlus))) := sorry
