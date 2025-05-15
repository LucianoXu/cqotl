
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import LeanVeri.Projection
import LeanVeri.LinearMapPropositions
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Trace

open Complex LinearMap Matrix FiniteDimensional

noncomputable section
variable {E : Type}

variable? [HilbertSpace ℂ E] => [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [FiniteDimensional ℂ E]

-- Define a finite-dimensional Hilbert space E over ℂ
@[reducible] def H2 : Type  := Fin 2 → ℂ

namespace H2
-- Instance declarations to make H2 a Hilbert space
instance : AddCommGroup H2 := Pi.addCommGroup
instance : Module ℂ H2 := Pi.module _ _ _
instance : NormedAddCommGroup H2 := Pi.normedAddCommGroup
instance : InnerProductSpace ℂ H2 := Pi.innerProductSpace ℂ (fun _ => ℂ)

-- The standard/computational basis vectors |0⟩ and |1⟩
def ket0 : H2 := fun i => if i = 0 then 1 else 0
def ket1 : H2 := fun i => if i = 1 then 1 else 0

-- Square root notation
local notation "√2" => Real.sqrt 2

-- The hadamard basis vectors |+⟩ and |-⟩
def ketplus   : H2 := ((1 : ℂ) / √2 : ℂ) • (ket0 + ket1)
def ketminus  : H2 := ((1 : ℂ) / √2 : ℂ) • (ket0 - ket1)

-- Inner product calculations
@[simp] lemma inner_apply (x y : H2) : ⟨x, y⟩ = ∑ i, (x i) * (y i) := rfl

-- Proof that ket0 and ket1 form an orthonormal basis
lemma is_orthonomal_basis_v0_v1 : OrthonormalBasis ℂ H2 (ket0 : Fin 2 → ℂ) (ket1 : Fin 2 → ℂ)

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

/-
  (|-><-|,|+><+|) ≥ (0, 1/2I + |1><1|)
  Proof. Same pattern as the one above.
-/
