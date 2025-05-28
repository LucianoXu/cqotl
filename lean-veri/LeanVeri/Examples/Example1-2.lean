/-
Copyright (c) 2025 Jam Khan. All rights reserved.
Authors: Jam Khan
-/
import LeanVeri.Commons
import LeanVeri.InfValPred
import LeanVeri.LinearMapPropositions
import LeanVeri.OuterProduct

/-
Proof obligation:
  ∀ ρ ∈ |+⟩⟨+|,
  ∀ i ∈ {0, 1},
    tr(|i⟩⟨i|ρ) = 1/2
Proof.
  Let ρ be s.t. supp(ρ) ⊆ im(|+⟩⟨+|),
  Let i be s.t. i ∈ {0, 1},

  `=` tr(|i⟩⟨i|ρ)
  `=` ∑ⱼ ⟨j|i⟩⟨i|ρ|j⟩, where j ∈ {0, 1}
  `=` ∑ⱼ ⟨j|i⟩⟨i|ρ|j⟩, where j ∈ {0, 1}
  `=` ∑ⱼ δij · ⟨i|ρ|j⟩, where δij = 1, i = j
                                  = 0, otherwise
  By cases on i
  `case: i = 0`
    `=` ⟨0|ρ|0⟩
    `=` Need to prove ⟨0|ρ|0⟩ = 1/2, ∀ ρ be s.t. supp(ρ) ⊆ im(|+⟩⟨+|)
    -- Since ρ is a density matric, then tr(ρ) = 1 and
      ρ = λ|+⟩⟨+| as supp(ρ) ⊆ im(|+⟩⟨+|).
      tr(λ|+⟩⟨+|) = 1 ↔ λ = 1
      Hence, ρ = |+⟩⟨+|
    `=` ⟨0|ρ|0⟩
    `=` ⟨0|+⟩⟨+|0⟩
    `=` ‖⟨0|+⟩‖² = 1/2 (Proved.)
  `case: i = 1`
    `=` ⟨1|ρ|1⟩
    `=` Need to prove ⟨1|ρ|1⟩ = 1/2, ∀ ρ be s.t. supp(ρ) ⊆ im(|+⟩⟨+|)
    `=` WLOG, ‖⟨1|+⟩‖² = 1/2 (Proved.)


Auxillary lemma:
  supp(ρ) ⊆ im(|+⟩⟨+|) → ρ = λ|+⟩⟨+| for some λ ∈ ℂ
Informal proof:
  By spectral decomposition,
  Let ρ = ∑ₖ λₖ • |ψₖ⟩⟨ψₖ|,
            where (λₖ,|ψₖ⟩) are non-zero eigen-value and eigen-vector

  Since supp(ρ) = span({|ψᵢ⟩ : ρ|ψᵢ⟩ = λᵢ|ψᵢ⟩, where λᵢ ≠ 0})
  Hence, |ψₖ⟩ ∈ supp(ρ)

  im(|+⟩⟨+|) = span({|+⟩}) as |+⟩⟨+| is a rank-1 projector (Need to prove this lemma, but doable)

  So, |ψₖ⟩ ∈ supp(ρ) ⊆ span({|+⟩})
  Hence, |ψₖ⟩ = cₖ • |+⟩ for some cₖ ∈ ℂ

  Now,
  `=` ρ
  `=` ∑ₖ λₖ • |ψₖ⟩⟨ψₖ|
  `=` ∑ₖ λₖ • (cₖ • |+⟩)(cₖ* • ⟨+|)
  `=` ∑ₖ λₖ • cₖcₖ* • |+⟩⟨+|
  `=` (∑ₖ λₖ • cₖcₖ*) • |+⟩⟨+|
  `=` λ • |+⟩⟨+|, where λ = (∑ₖ λₖ • cₖcₖ*) ∈ ℂ
-/
