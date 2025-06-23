import LeanVeri.Commons
import LeanVeri.LinearMapPropositions
import LeanVeri.ProjectionSubmodule
import LeanVeri.OuterProduct
import LeanVeri.Spectrum
import LeanVeri.Trace

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

def μ  : Bool → 𝕜
  | _ => 1/2

def P0 : 𝕜² →ₗ[𝕜] 𝕜² := ketbra0

noncomputable def vPlus : 𝕜² := ketP

lemma aux (T : 𝕜² →ₗ[𝕜] 𝕜²) (hT : T.isDensityOperator)
    (h : T.toSubmodule ≤ ketbraP.toSubmodule) :
    T.isProjection := by
  have hTsymm := hT.left.IsSymmetric
  have h2 : Module.finrank 𝕜 𝕜² = 2 := finrank_euclideanSpace_fin (𝕜 := 𝕜) (n := 2)
  have h' : T.toSubmodule = ketbraP.toSubmodule := by
    apply Submodule.eq_of_le_of_finrank_eq h
    rw [toSubmodule_ketbraP_eq_span_ketP, finrank_span_singleton neZero_ketP]
    have hdim := Submodule.finrank_mono h
    rw [toSubmodule_ketbraP_eq_span_ketP, finrank_span_singleton neZero_ketP] at hdim
    refine (Nat.le_antisymm_iff.mpr (And.intro hdim ?_))
    rw [Submodule.one_le_finrank_iff]
    intro hT'
    have htr : LinearMap.trace 𝕜 𝕜² T = 0 := by
      rw [T.eq_zero_of_toSubmodule_eq_bot hT']
      apply LinearMap.map_zero
    rw [hT.right] at htr
    simp_all
  rw [toSubmodule_ketbraP_eq_span_ketP] at h
  unfold LinearMap.toSubmodule at h'
  rw [Submodule.orthogonalComplement_eq_orthogonalComplement] at h'
  have hsum : 1 = hTsymm.eigenvalues h2 0 + hTsymm.eigenvalues h2 1 := by
    have hsum' := hTsymm.re_trace_eq_sum_eigenvalues h2
    rw [hT.right, RCLike.one_re] at hsum'
    rw [hsum']
    exact Fin.sum_univ_two (hTsymm.eigenvalues h2)
  have hdim : Module.finrank 𝕜 (LinearMap.ker T) = 1 := by
    rw [h', ker_ketbraP_eq_span_ketM, finrank_span_singleton neZero_ketM]
  have heigen := hTsymm.zero_eigenvalue_zero_or_one_of_finrank_ker_eq_one_of_finrank_eq_two h2 hdim
  rw [hT.left.isProjection_iff_eigenvalues_eq_zero_or_one h2]
  intro i
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases heigen with (h0 | h1) <;> fin_cases i <;> simp_all

lemma aux2 (T : 𝕜² →ₗ[𝕜] 𝕜²) (hT : T.isDensityOperator)
    (h : T.toSubmodule ≤ ketbraP.toSubmodule) :
    T = ketbraP := by
  have h2 : Module.finrank 𝕜 𝕜² = 2 := finrank_euclideanSpace_fin (𝕜 := 𝕜) (n := 2)
  have hdim : Module.finrank 𝕜 T.toSubmodule = Module.finrank 𝕜 (ketbraP : 𝕜² →ₗ[𝕜] 𝕜²).toSubmodule := by
    apply le_antisymm (Submodule.finrank_mono h)
    rw [finrank_toSubmodule_ketbraP, Submodule.one_le_finrank_iff, ne_eq, ← T.eq_zero_iff_toSubmodule_eq_bot]
    exact hT.neZero
  have h' : T.toSubmodule = ketbraP.toSubmodule := Submodule.eq_of_le_of_finrank_eq h hdim
  have hTproj : T.isProjection := aux T hT h
  exact (hTproj.eq_iff_toSubmodule_eq isProjection_ketbraP).mpr h'


lemma obligation (ρ1 : 𝕜² →ₗ[𝕜] 𝕜²) (h1 : (LinearMap.isDensityOperator ρ1))
    (h2 : ((LinearMap.toSubmodule ρ1) ≤ (LinearMap.toSubmodule ketbraP))) :
    ((((LinearMap.trace 𝕜) 𝕜²) (P0 * ρ1)) = (μ false)) :=
  calc
    LinearMap.trace 𝕜 𝕜² (P0 * ρ1)
      = LinearMap.trace 𝕜 𝕜² (ketbra0 * ketbraP) := by rw [P0, aux2 ρ1 h1 h2]
    _ = LinearMap.trace 𝕜 𝕜² (inner 𝕜 (ket0 : 𝕜²) ketP • ket0braP) := by
          unfold ketbra0 ketbraP ket0braP
          rw [outerProduct_mul_outerProduct_eq_inner_smul_outerProduct]
    _ = LinearMap.trace 𝕜 𝕜² ((1/√2 : 𝕜) • ket0braP) := by rw [inner_ket0_ketP]
    _ = (1/√2 : 𝕜) * LinearMap.trace 𝕜 𝕜² ket0braP := by simp [map_smul]
    _ = (1/√2 : 𝕜) * (1/√2 : 𝕜) := by simp [trace_ket0braP]
    _ = (1/2 : 𝕜) := by
          rw [one_div_mul_one_div_rev, ← RCLike.ofReal_mul]
          simp [RCLike.ofReal_ofNat]
    _ = μ false := rfl
