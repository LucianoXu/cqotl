import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.LinearMap.Defs
-- import LeanVeri.LinearMapPropositions

open scoped ComplexOrder

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]
variable? [HilbertSpace 𝕜 F] => [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [FiniteDimensional 𝕜 F]

namespace LinearMap

/-- Positive semidefinite operators. -/
def isPositiveSemiDefinite (T : E →ₗ[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ RCLike.re (inner 𝕜 (T x) x)

/-- The outer product of two vectors. -/
def outerProduct (φ : E) (ψ : E) : E →ₗ[𝕜] E where
  toFun := fun χ => (inner 𝕜 ψ χ : 𝕜) • φ
  map_add' := by
    intro χ η
    rw [← Module.add_smul]
    rw [inner_add_right ψ χ η]
  map_smul' := by
    intro m χ
    rw [RingHom.id_apply]
    rw [inner_smul_right_eq_smul ψ χ m]
    exact IsScalarTower.smul_assoc m (inner 𝕜 ψ χ) φ

end LinearMap

open scoped TensorProduct

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional 𝕜 F]

namespace BasicProperties
-- This lemma shows the `Scalar product of same normalized vectors` property `⟨φ|φ⟩ = 1`.
lemma scalar_product_eq_one (_ : 𝕜) (φ : E) (A : E →ₗ[𝕜] E) (_ : LinearMap.isPositiveSemiDefinite A) :
    norm φ = 1 → inner 𝕜 φ φ = 1 :=
    by  intro H
        refine (inner_eq_one_iff_of_norm_one ?_ ?_).mpr rfl
        repeat assumption

-- This lemma shows the `Scalar product` property `⟨φ|(c•A)|φ⟩ = c * ⟨φ|A|φ⟩`.
lemma scalar_product (c : 𝕜) (φ : E) (A : E →ₗ[𝕜] E) (_ : LinearMap.isPositiveSemiDefinite A) :
  inner 𝕜 φ ((c • A) φ) = c * inner 𝕜 φ (A φ) := by
    rw [@LinearMap.smul_apply, @inner_smul_right]

end BasicProperties

open scoped InnerProduct
noncomputable section

@[reducible] def C2 : Type := EuclideanSpace ℂ (Fin 2)

namespace C2
-- Define the standard basis vectors |0⟩ and |1⟩
def ket0 : C2 := !₂[1, 0]
def ket1 : C2 := !₂[0, 1]

-- Define the scalar 1/√2 as a complex number
local notation "inv_sqrt2" => (1 : ℂ) / ((Real.sqrt 2) : ℂ)

-- The hadamard basis vectors |+⟩ and |-⟩ in terms of the computational basis
def ketplus   : C2 := inv_sqrt2 • (ket0 + ket1) -- (1/√2) * (|0> + |1>)
def ketminus  : C2 := inv_sqrt2 • (ket0 - ket1) -- (1/√2) * (|0> - |1>)

noncomputable def ket0_bra0         : C2 →ₗ[ℂ] C2 := LinearMap.outerProduct ket0  ket0
noncomputable def ket1_bra1         : C2 →ₗ[ℂ] C2 := LinearMap.outerProduct ket1  ket1
noncomputable def ketplus_braplus   : C2 →ₗ[ℂ] C2 := LinearMap.outerProduct ketplus ketplus
noncomputable def ketminus_braminus : C2 →ₗ[ℂ] C2 := LinearMap.outerProduct ketminus ketminus

-- Prove basic inner products for calculuations
lemma inner_ket0_ket0       : inner ℂ ket0 ket0          = 1 :=
  by  have h1 : norm ket0 = 1 :=
        by  rw [ket0]
            rw [@PiLp.norm_eq_of_L2]
            simp only [WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue,
              Matrix.cons_val_zero, norm_one, one_pow, Matrix.cons_val_one, Matrix.cons_val_fin_one,
              norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
              Real.sqrt_one]
      exact (inner_eq_one_iff_of_norm_one h1 h1).mpr rfl
lemma inner_ket1_ket1       : inner ℂ ket1 ket1          = 1 :=
  by  have h1 : norm ket1 = 1 :=
        by  rw [ket1]
            rw [@PiLp.norm_eq_of_L2]
            simp only [WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue,
              Matrix.cons_val_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              zero_pow, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_one, one_pow, zero_add,
              Real.sqrt_one]
      exact (inner_eq_one_iff_of_norm_one h1 h1).mpr rfl
lemma inner_ketplus_plus    : inner ℂ ketplus ketplus    = 1 :=
  by
    have h1 : norm ketplus = 1 := by
      calc
        norm ketplus = norm (inv_sqrt2 • (ket0 + ket1))     := rfl
        _            = norm (inv_sqrt2 • (!₂[1,1] : C2))    := by
          have h2 : (!₂[1, 0] : C2) + (!₂[0, 1] : C2) = !₂[1, 1] := by
            ext i
            fin_cases i
            · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, WithLp.equiv_symm_pi_apply,
              Matrix.cons_val_zero, add_zero]
            · simp only [Fin.mk_one, Fin.isValue, PiLp.add_apply, WithLp.equiv_symm_pi_apply,
              Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add]
          rw [ket0, ket1, h2]
        _            = 1                                    := by
          rw [@norm_smul]
          simp only [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs]
          rw [@PiLp.norm_eq_of_L2]
          simp only [WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue,
            Matrix.cons_val_zero, norm_one, one_pow, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          ring_nf
          refine (inv_mul_eq_one₀ ?_).mpr ?_
          · simp only [ne_eq, abs_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
            OfNat.ofNat_ne_zero, not_false_eq_true]
          · simp only [abs_eq_self, Real.sqrt_nonneg]
    exact (inner_eq_one_iff_of_norm_one h1 h1).mpr rfl
lemma inner_ketminus_minus  : inner ℂ ketminus ketminus  = 1 :=
  by
    have h1 : norm ketminus = 1 := by
      calc
        norm ketminus = norm (inv_sqrt2 • (ket0 - ket1))    := rfl
        _            = norm (inv_sqrt2 • (!₂[1, -1] : C2))    := by
          have h2 : (!₂[1, 0] : C2) - (!₂[0, 1] : C2) = !₂[1, -1] := by
            ext i
            fin_cases i
            · simp only [Fin.zero_eta, Fin.isValue, PiLp.sub_apply, WithLp.equiv_symm_pi_apply,
              Matrix.cons_val_zero, sub_zero]
            · simp only [Fin.mk_one, Fin.isValue, PiLp.sub_apply, WithLp.equiv_symm_pi_apply,
              Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_sub]
          rw [ket0, ket1, h2]
        _            = 1                                    := by
          rw [@norm_smul]
          simp only [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs]
          rw [@PiLp.norm_eq_of_L2]
          simp only [WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue,
            Matrix.cons_val_zero, norm_one, one_pow, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          ring_nf
          refine (inv_mul_eq_one₀ ?_).mpr ?_
          · simp only [ne_eq, abs_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
            OfNat.ofNat_ne_zero, not_false_eq_true]
          · simp only [norm_neg, norm_one, one_pow]
            ring_nf
            simp only [abs_eq_self, Real.sqrt_nonneg]
    exact (inner_eq_one_iff_of_norm_one h1 h1).mpr rfl


end C2

open C2

-- The identity operator on C2
local notation "I" => (LinearMap.id : C2 →ₗ[ℂ] C2)

#check I
#check ketminus_braminus
variable {φ : C2}
#check  ketminus_braminus (φ)


lemma obligation : ∀ {φ : C2}, inner ℂ φ (ketminus_braminus φ) = inner ℂ (ketminus_braminus φ) φ := by
  intro
  rw [@PiLp.inner_apply]
  simp only [RCLike.inner_apply, Fin.sum_univ_two, Fin.isValue, PiLp.inner_apply]

  sorry

-- section LownerOrder

-- open scoped ComplexOrder


/-
  Löwner order of (|-><-|,|+><+|) is greater than (0, 1/2I + |0><0|)

  (|-><-|,|+><+|) >= (0, 1/2I + |0><0|)
  Let
    A₁ ≃ (Xₐ¹, Pₐ¹), where  A₁                      ∈ Pos∞(ℍ),
                            Xₐ¹ = |-⟩⟨-|            ∈ S(ℍ),
                            Pₐ¹ = |+⟩⟨+|            ∈ Pos(ℍ)
                            s.t. Pₐ¹Xₐ¹ = 0 (Orthogonal)
    A₂ ≃ (Xₐ², Pₐ²), where  A₂                      ∈ Pos∞(ℍ),
                            Xₐ² = O                 ∈ S(ℍ),
                            Pₐ² = 1⧸2 ⬝ I + |0⟩⟨0|   ∈ Pos(ℍ)
                            s.t. Pₐ²Xₐ² = 0 (Orthogonal)

  Obligation:
    ∀ |ψ⟩ ∈ ℍ,  ⟨ψ|(Pₐ¹ + (+∞ . Xₐ¹))|ψ⟩ ≥ ⟨ψ|(Pₐ² + (+∞ . Xₐ²))|ψ⟩
  Proof.
    By subs:
      - ⟨ψ|(|+⟩⟨+| + (+∞ . |-⟩⟨-|))|ψ⟩ ≥ ⟨ψ|(1⧸2 ⬝ I + |0⟩⟨0| + (+∞ . O))|ψ⟩
    By simp:
      - ⟨ψ|+⟩⟨+|ψ⟩ + ⟨ψ|(+∞ . |-⟩⟨-|)|ψ⟩ ≥ ⟨ψ|(1⧸2 ⬝ I)|ψ⟩ + ⟨ψ|0⟩⟨0|ψ⟩ + ⟨ψ|(+∞ . O)|ψ⟩
      - ⟨ψ|+⟩⟨+|ψ⟩ + +∞ . ⟨ψ|-⟩⟨-|ψ⟩ ≥ 1⧸2 ⬝ ⟨ψ|I|ψ⟩ + ⟨ψ|0⟩⟨0|ψ⟩ + (+∞ .⟨ψ|O|ψ⟩)
      - ⟨ψ|+⟩⟨+|ψ⟩ + +∞ . ⟨ψ|-⟩⟨-|ψ⟩ ≥ 1⧸2 ⬝ ⟨ψ|I|ψ⟩ + ⟨ψ|0⟩⟨0|ψ⟩ + (+∞ .⟨ψ|O|ψ⟩)
      - ⟨ψ|+⟩⟨+|ψ⟩ + +∞ . ⟨ψ|-⟩⟨-|ψ⟩ ≥ 1⧸2 ⬝ ⟨ψ|ψ⟩   + ⟨ψ|0⟩⟨0|ψ⟩ + (+∞ . 0)
      - ⟨ψ|+⟩⟨+|ψ⟩ + +∞ . ⟨ψ|-⟩⟨-|ψ⟩ ≥ 1⧸2 ⬝ ⟨ψ|ψ⟩   + ⟨ψ|0⟩⟨0|ψ⟩ + 0
      - ‖⟨ψ|+⟩‖²   + +∞ . ‖⟨ψ|-⟩‖²   ≥ 1⧸2 ⬝ ⟨ψ|ψ⟩   + ‖⟨ψ|0⟩‖²

      By cases on ‖⟨ψ|-⟩‖²
      · case: ‖⟨ψ|-⟩‖² = 0
        - ‖⟨ψ|+⟩‖² ≥ 1⧸2 ⬝ ⟨ψ|ψ⟩ + ‖⟨ψ|0⟩‖²
        - Have lemma AUX: ‖⟨ψ|-⟩‖² = 0 ↔ ∃ λ ∈ ℂ, |ψ⟩ = λ|+⟩ (Need proof)
          Have |ψ⟩ = λ|+⟩ for some λ ∈ ℂ (by lemma AUX)
          - ‖⟨ψ|+⟩‖² ≥ 1⧸2 ⬝ ⟨ψ|ψ⟩ + ‖⟨ψ|0⟩‖²
          - By simp,
              - ‖⟨+|λ|+⟩‖² ≥ 1⧸2 ⬝ λ²⟨+|+⟩ + ‖⟨+|λ|0⟩‖²
              - λ² ≥ 1/2 · λ² + 1/2 . λ²
              - λ² ≥ λ² (Trivially True)

      · case: ‖⟨ψ|-⟩‖² ≠ 0
        - +∞ ≥ 1⧸2 ⬝ ⟨ψ|ψ⟩ + ‖⟨ψ|0⟩‖² (Trivially True)
-/



end
