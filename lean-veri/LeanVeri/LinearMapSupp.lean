
import LeanVeri.Projection
import LeanVeri.LinearMapPropositions


variable {𝕜 E : Type*} [RCLike 𝕜]

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]

-- Proposition A.3 (Properties of the Support)
namespace SupportProp

def supp (P : E →ₗ[𝕜] E) : Submodule 𝕜 E := (LinearMap.ker P)ᗮ

lemma ker_add (P Q : E →ₗ[𝕜] E) (hP : LinearMap.isPositiveSemiDefinite P) (hQ : LinearMap.isPositiveSemiDefinite Q):
  (LinearMap.ker (P + Q)) = (LinearMap.ker P) ⊓ (LinearMap.ker Q)               := by
  rcases hP with ⟨hP_self, hP_re⟩
  rcases hQ with ⟨hQ_self, hQ_re⟩
  ext x
  have : RCLike.re (inner 𝕜 (P x) x) + RCLike.re (inner 𝕜 (Q x) x) = RCLike.re (inner 𝕜 ((P + Q) x) x) := by
    rw [@LinearMap.add_apply, @inner_add_left, @AddMonoidHom.map_add]
  simp only [LinearMap.mem_ker, LinearMap.add_apply, Submodule.mem_inf]
  constructor
  · intro h
    rw [@LinearMap.add_apply, h, @inner_re_zero_left] at this
    have hPx : RCLike.re (inner 𝕜 (P x) x) = 0 := by
      apply le_antisymm
      · have hsum_zero := this
        have hQ_nonneg := hQ_re x
        linarith
      · exact hP_re x
    have hQx : RCLike.re (inner 𝕜 (Q x) x) = 0 := by
      apply le_antisymm
      · have hsum_zero := this
        have hQ_nonneg := hP_re x
        linarith
      · exact hQ_re x
    sorry
  · intro h
    simp_all only [inner_zero_left, map_zero, add_zero, LinearMap.add_apply]


lemma ker_union (P Q : E →ₗ[𝕜] E) (hP : LinearMap.isPositiveSemiDefinite P) (hQ : LinearMap.isPositiveSemiDefinite Q):
  (LinearMap.ker P ⊓ LinearMap.ker Q)ᗮ = (LinearMap.ker P)ᗮ ⊔ (LinearMap.ker Q)ᗮ := by
  ext x
  constructor
  · intro H
    rw [@Submodule.mem_orthogonal'] at H
    simp_all only [Submodule.mem_inf, LinearMap.mem_ker, and_imp]
    refine Submodule.mem_sup_right ?_
    refine (Submodule.mem_orthogonal' (LinearMap.ker Q) x).mpr ?_
    sorry
  · intro H
    sorry

lemma supp_add (P Q : E →ₗ[𝕜] E) (hP : LinearMap.isPositiveSemiDefinite P) (hQ : LinearMap.isPositiveSemiDefinite Q) :
    supp (P + Q) = supp (P) ⊔ supp (Q)  := by
    rw [supp]
    rw [supp]
    rw [supp]
    rw [ker_add]
    rw [ker_union]
    · apply hP
    · apply hQ
    · apply hP
    · apply hQ

end SupportProp
