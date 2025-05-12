
import LeanVeri.Projection
import LeanVeri.LinearMapPropositions
import LeanVeri.Properties

variable {𝕜 E : Type*} [RCLike 𝕜]

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]

-- Proposition A.3 (Properties of the Support)
namespace SupportProp

def supp (P : E →ₗ[𝕜] E) : Submodule 𝕜 E := (LinearMap.ker P)ᗮ

lemma ker_add (P Q : E →ₗ[𝕜] E) (hP : LinearMap.isProjection P) (hQ : LinearMap.isProjection Q):
  (LinearMap.ker (P + Q)) = (LinearMap.ker P) ⊓ (LinearMap.ker Q)               := by
  have hPadj: P.adjoint = P := by
    exact AlgebraicProperties.adjointeql P hP
  have hQadj: Q.adjoint = Q := by
    exact AlgebraicProperties.adjointeql Q hQ
  rcases hP with ⟨hP_posdef, hP_proj⟩
  rcases hQ with ⟨hQ_posdef, hQ_proj⟩
  rcases hP_posdef with ⟨hP_self, hP_re⟩
  rcases hQ_posdef with ⟨hQ_self, hQ_re⟩
  ext x
  have : inner 𝕜 (P x) x + inner 𝕜 (Q x) x = inner 𝕜 ((P + Q) x) x := by
    simp only [LinearMap.add_apply]
    rw [@inner_add_left]
  simp only [LinearMap.mem_ker, LinearMap.add_apply, Submodule.mem_inf]
  constructor
  · intro h
    rw [LinearMap.add_apply, h, inner_zero_left] at this
    have hPx1 : inner 𝕜 (P x) x = inner 𝕜 (P x) (P x) :=
      calc
        inner 𝕜 (P x) x   = inner 𝕜 ((P ∘ₗ P) x) x  := by  rw [hP_proj]
        _                   = inner 𝕜 (P x) (P x)  := by  simp only [LinearMap.coe_comp, Function.comp_apply]
                                                          nth_rw 1 [← hPadj]
                                                          rw [@LinearMap.adjoint_inner_left]
    have hQx1 : inner 𝕜 (Q x) x = inner 𝕜 (Q x) (Q x) :=
      calc
        inner 𝕜 (Q x) x   = inner 𝕜 ((Q ∘ₗ Q) x) x  := by  rw [hQ_proj]
        _                 = inner 𝕜 (Q x) (Q x)    := by  simp only [LinearMap.coe_comp, Function.comp_apply]
                                                          nth_rw 1 [← hQadj]
                                                          rw [@LinearMap.adjoint_inner_left]
    have hPx_re : 0 ≤ RCLike.re (inner 𝕜 (P x) (P x)) := by
      rw [← hPx1]
      exact hP_re x
    have hQx_re : 0 ≤ RCLike.re (inner 𝕜 (Q x) (Q x)) := by
      rw [← hQx1]
      exact hQ_re x
    have hPx : inner 𝕜 (P x) x = 0 := by
      rw [hPx1] at this
      have : inner 𝕜 (P x) (P x) + inner 𝕜 (Q x) (Q x) = 0 := by
        rw [hQx1] at this
        exact this
      sorry
    have hQx : inner 𝕜 (Q x) x = 0 := by
      sorry
    rw [hPx1, inner_self_eq_zero] at hPx
    rw [hQx1, inner_self_eq_zero] at hQx
    exact ⟨hPx, hQx⟩
  · intro h
    simp_all only [inner_zero_left, map_zero, add_zero, LinearMap.add_apply]


lemma ker_union (P Q : E →ₗ[𝕜] E) (hP : LinearMap.isProjection P) (hQ : LinearMap.isProjection Q):
  (LinearMap.ker P ⊓ LinearMap.ker Q)ᗮ = (LinearMap.ker P)ᗮ ⊔ (LinearMap.ker Q)ᗮ := by
  ext x
  constructor
  · intro H
    rw [@Submodule.mem_orthogonal'] at H
    simp_all only [Submodule.mem_inf, LinearMap.mem_ker, and_imp]
    have hQ_decomp : x = (x - Q x) + Q x:= by simp
    rw [hQ_decomp]
    apply Submodule.add_mem_sup
    · rw [@Submodule.mem_orthogonal']
      intro u hu
      rw [LinearMap.mem_ker] at hu
      have : u ∈ LinearMap.ker P ⊓ LinearMap.ker Q := by
        refine Submodule.mem_inf.mpr ?_
        constructor
        · exact hu
        · apply H at hu
          rw [@LinearMap.mem_ker]

          refine LinearMap.mem_ker.mpr ?_
          sorry
      sorry
    · rw?
      sorry
  · intro H
    sorry

lemma supp_add (P Q : E →ₗ[𝕜] E) (hP : LinearMap.isProjection P) (hQ : LinearMap.isProjection Q) :
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
