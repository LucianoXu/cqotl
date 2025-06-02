#check 1

-- Informal lean-calc proof for all the proof obligations of examples in the paper.

/-
Example 1

Side condition Γ₁ includes four parts
  • id is a bijection.
  `Proof. Trivial. Directly in the OCaml prover.`
  • true.
  `Proof. Trivial. Directly in the OCaml prover.`
  1.1.3.
    true →
      ∀ ρ ∈ |+⟩q⟨+|,
        ∀ i ∈ {0, 1}, tr(|i⟩q⟨i|ρ) = 1/2;
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
        -- Since ρ is a density matrix, then tr(ρ) = 1 and
        -- ρ = λ|+⟩⟨+| as supp(ρ) ⊆ im(|+⟩⟨+|).
          tr(λ|+⟩⟨+|) = 1 ↔ λ = 1
          Hence, ρ = |+⟩⟨+|
        `=` ⟨0|ρ|0⟩
        `=` ⟨0|+⟩⟨+|0⟩
        `=` ‖⟨0|+⟩‖² = 1/2        (Proved.)
      `case: i = 1`
        `=` ⟨1|ρ|1⟩
        `=` Need to prove ⟨1|ρ|1⟩ = 1/2, ∀ ρ be s.t. supp(ρ) ⊆ im(|+⟩⟨+|)
        `=` WLOG, ‖⟨1|+⟩‖² = 1/2  (Proved.)

    Auxiliary lemma:
      supp(ρ) ⊆ im(|+⟩⟨+|) → ρ = λ|+⟩⟨+| for some λ ∈ ℂ
    Proof.
      By spectral decomposition,
      Let ρ = ∑ₖ λₖ • |ψₖ⟩⟨ψₖ|,
                where (λₖ,|ψₖ⟩) are non-zero eigenvalue and eigen-vector

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
    Qed.

  1.1.4.
    true → |+⟩q⟨+| ⊨ ∧ᵢ (¬ (i = i) → (|i⟩q⟨i| → ⊥))
  Proof.
    First, we need simplification on the OCaml prover side.
      - `labelled dirac` to `dirac`
    `=` true → |+⟩⟨+| ⊨ ∧ᵢ (¬ (i = i) → (|i⟩⟨i| → ⊥))
      - `applying lemma 6.3`
    `Note: Above steps can be directly done in the OCaml prover`

    `=` ∀j. ¬ (j = j) ⇒ (|+⟩⟨+| if ¬ (j = j) → true else Ø) ⊆ (|j⟩⟨j| → ⊥)
      - `intro j`
    `=` ¬ (j = j) ⇒ (|+⟩⟨+| if ¬ (j = j) → true else Ø) ⊆ (|j⟩⟨j| → ⊥)
      - `¬ (j = j) ≅ ¬ (True) ≅ False `
    `=` False ⇒ (|+⟩⟨+| if ¬ (j = j) → true else Ø) ⊆ (|j⟩⟨j| → ⊥)
      - `intro h_false`
    `=` (|+⟩⟨+| if ¬ (j = j) → true else Ø) ⊆ (|j⟩⟨j| → ⊥)
      - `contradiction using h_false`
  Qed.

Side condition Γ₂ includes one part:
• (false → ⊥) ∧ (true → |0⟩⟨0|) ⊨ true → |0⟩⟨0|
  `Proof`
  `=` (true) ∧ (true → |0⟩⟨0|) ⊨ true → |0⟩⟨0|
  `=` (true → |0⟩⟨0|) ⊨ true → |0⟩⟨0|
  `=` true ⇒ |0⟩⟨0| ⊆ |0⟩⟨0| (`holds by rfl`)
-/

/-
Example 2

Side condition Γ₁ includes three parts:
  • id is a bijection
  `Proof`. Holds in the OCaml prover directly.
  • ¬ (x = x') ∨ x = x' holds.
  `Proof`.
  `¬ (x = x') ∨ x = x'`
    `=` `¬ P ∨ P`, where `P = (x = x')`
    `=` `holds by cases on P`.

Side condition Γ₂ includes three parts:
  • id is a bijection
  `Proof`. Holds in the OCaml prover directly.
  • true holds
  • true ⇒
      ∀ ρ ∈ P',
        • |0⟩_q1⟨0| tr₂(ρ)|0⟩q₁⟨0|(Psym[q₂, q₂'])#|0⟩q1⟨0|tr₁(ρ)|0⟩⟨0|
        • |1⟩_q1⟨1| tr₂(ρ)|1⟩q₁⟨1|(Uq2 ⬝ Psym[q₂, q₂'] Uq2†)#|0⟩q1⟨0|tr₁(ρ)|0⟩⟨0|
      where
        P' = (|00⟩𝑞1𝑞1'⟨00| ∧ 𝑃𝑠𝑦𝑚 [𝑞2, 𝑞′2]) ∨ (|11⟩𝑞1𝑞1'⟨1| ∧ 𝑈𝑞2 𝑃𝑠𝑦𝑚[𝑞2, 𝑞′2]𝑈𝑞2† ).
-/
/-
  Lemma 6.3 (ENTAILMENTS).
  We write ∧ᵢ(bᵢ → Pᵢ) ⊨ ∧ⱼ(cⱼ → Qⱼ) for the entailment relation. By employing solvers such as SMT,
  we can further reduce the checking ∧ᵢ(bᵢ → Pᵢ) ⊨ ∧ⱼ(cⱼ → Qⱼ) by:
    ∀j. cⱼ ⇒ (∧ₖ Pₖ) ⊆ Qⱼ, where k ∈ {i | cⱼ → bᵢ}.

-/

/-
Example 4
  
  Side condition Γ₁ includes:
  • ((x = 0 → ⊥) ∧ (x = 1 → |1⟩⟨1|)) ∧ (true → |0⟩q'⟨0|)

-/
