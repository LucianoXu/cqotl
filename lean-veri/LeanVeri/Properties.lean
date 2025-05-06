/-
Copyright (c) 2025 Jam Kabeer Ali Khan. All rights reserved.
Authors: Jam Kabeer Ali Khan
-/

import LeanVeri.Projection
import LeanVeri.LinearMapPropositions
import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {𝕜 E : Type*} [RCLike 𝕜]
-- notation:100 T "⊗ₗ" N:100 => TensorProduct.map T N

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]
omit [CompleteSpace E]


open scoped TensorProduct

-- lemma A.7
namespace BasicProperties

/-
This lemma shows the `Scalar product` property `⟨φ|(c•A)|φ⟩ = c * ⟨φ|A|φ⟩`.
-/
lemma scalar_product (c : 𝕜) (φ : E) (A : E →ₗ[𝕜] E) (_ : LinearMap.isPositiveSemiDefinite A) :
  inner 𝕜 φ ((c • A) φ) = c * inner 𝕜 φ (A φ) := by
    rw [@LinearMap.smul_apply, @inner_smul_right]

/-
This lemma shows the `Addition` property `⟨φ|(A₁ + A₂)|φ⟩ = ⟨φ|A₁|φ⟩ + ⟨φ|A₁|φ⟩`.
-/
lemma addition (φ : E) (A₁ A₂ : E →ₗ[𝕜] E) (_ : LinearMap.isPositiveSemiDefinite A₁) (_ : LinearMap.isPositiveSemiDefinite A₂) :
  inner 𝕜 φ ((A₁ + A₂) φ) = inner 𝕜 φ (A₁ φ) + inner 𝕜 φ (A₂ φ) := by
    rw [@LinearMap.add_apply, @inner_add_right]

/-
This lemma shows the `Tensor` product property `(⟨φ₁|⨂⟨φ₂|)(A₁ ⨂ A₂)(|φ₁⟩⨂|φ₂⟩) = (⟨φ₁|A₁|φ₁⟩)·(⟨φ₂|A₂|φ₂⟩)`
-/
-- variable (φ₁ φ₂ : E)
-- #check (φ₁ ⊗ₗ φ₂)

/- Work-in progress!!!

lemma tensor_product
  (φ₁ φ₂ : E)
  (A₁ A₂ : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A₁)
  (_ : LinearMap.isPositiveSemiDefinite A₂)
  (h : ∀ x y x' y', inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y') :
  inner 𝕜 (φ₁ ⊗ₜ[𝕜] φ₂)
          ((TensorProduct.map A₁ A₂) (φ₁ ⊗ₜ[𝕜] φ₂)) =
    inner 𝕜 φ₁ (A₁ φ₁) * inner 𝕜 φ₂ (A₂ φ₂) := by
  sorry

-/
end BasicProperties
