/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Authors: Iván Renison
-/
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
Auxiliary lemma about summations.
-/

lemma sum_diag_eq (n : ℕ) (f : Fin n → Fin n → ℝ) :
    ∑i ∈ ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2), f i.1 i.2 =
    ∑i, f i i := by
  let diag := (@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2
  rw [← add_zero (∑i ∈ ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ i.1 = i.2), f i.1 i.2),
    ← show ∑i ∈ diagᶜ, (0 : ℝ) = 0 by exact Finset.sum_const_zero]
  have diagc : diagᶜ = ((@Finset.univ (Fin n × Fin n) _).filter fun i ↦ ¬i.1 = i.2) := by
    unfold diag
    simp
  rw [diagc, ← Finset.sum_ite, Fintype.sum_prod_type]
  simp
