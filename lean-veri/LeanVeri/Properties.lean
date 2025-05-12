/-
Copyright (c) 2025 Jam Kabeer Ali Khan. All rights reserved.
Authors: Jam Kabeer Ali Khan
-/

import LeanVeri.Projection
import LeanVeri.LinearMapPropositions
import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {𝕜 l n E F : Type*} [RCLike 𝕜] [RCLike l] [RCLike n] [CommSemiring n] [CommSemiring l]
-- notation:100 T "⊗ₗ" N:100 => TensorProduct.map T N

variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable? [HilbertSpace 𝕜 F] => [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable [FiniteDimensional 𝕜 E]
variable [FiniteDimensional 𝕜 F]

omit [CompleteSpace E]
omit [CompleteSpace F]
omit [FiniteDimensional 𝕜 F]

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

-- lemma A.8
namespace AlgebraicProperties


/- Auxilary lemma for adjoint-/
lemma adjointeql (T: E →ₗ[𝕜] E)
    (hT : LinearMap.isProjection T) : T.adjoint = T := by
    rw [← @LinearMap.isSelfAdjoint_iff']
    rcases hT with ⟨hT_posS, hT_proj⟩
    rcases hT_posS with ⟨hT_self, hT_inner⟩
    repeat assumption

/-
This lemma shows the `Zero_Multiplication` property `0A = 0`.
-/
lemma zero_mul
  (A : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A) :
    0 • A = (0 : E →ₗ[𝕜] E) :=
  zero_nsmul A

/-
This lemma shows the `One_Multiplication` property `1A = A`.
-/
lemma one_mul
  (A : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A) :
    1 • A = A :=
  one_nsmul A

/-
This lemma shows the `Mult_Associativity` property `a(bA) = (ab)A`.
-/
lemma mult_assoc
  (a b : 𝕜)
  (A : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A) :
    a • (b • A) = (a * b) • A :=
  smul_smul a b A

/-
This lemma shows the `Zero_Add_Identity` property `0 + A = A`.
-/
lemma zero_add
  (A : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A) :
    (0 : E →ₗ[𝕜] E) + A = A := by
  rw [add_eq_right]

/-
This lemma shows the `Add_Zero_Identity` property `A + 0 = A`.
-/
lemma add_zero
  (A : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A) :
    A + (0 : E →ₗ[𝕜] E) = A :=
  by rw [add_eq_left]

/-
This lemma shows the `Zero_Add_Add_Zero_Eqv` property `A + 0 = 0 + A`.
-/
lemma zero_add_add_zero_eq
  (A : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A) :
    A + (0 : E →ₗ[𝕜] E) = (0 : E →ₗ[𝕜] E) + A := by
  rw [add_zero, zero_add]; repeat assumption

/-
This lemma shows the `Add_Commutativity` property `A₁ + A₂ = A₂ + A₁`.
-/
lemma add_comm
  (A₁ A₂ : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A₁)
  (_ : LinearMap.isPositiveSemiDefinite A₂) :
    A₁ + A₂ = A₂ + A₁ := by
  rw [@AddCommMonoidWithOne.add_comm]

/-
This lemma shows the `Add_Right_Associativity` property `A₁ + A₂ + A₃ = A₁ + (A₂ + A₃)`.
-/
lemma add_right_associativity
  (A₁ A₂ A₃ : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A₁)
  (_ : LinearMap.isPositiveSemiDefinite A₂) :
    A₁ + A₂ + A₃ = A₁ + (A₂ + A₃) := by
  rw [@AddSemigroup.add_assoc]

/-
This lemma shows the `Add_Left_Associativity` property `A₁ + A₂ + A₃ = (A₁ + A₂) + A₃`.
-/
lemma add_left_associativity
  (A₁ A₂ A₃ : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A₁)
  (_ : LinearMap.isPositiveSemiDefinite A₂)
  (_ : LinearMap.isPositiveSemiDefinite A₃) :
    A₁ + A₂ + A₃ = (A₁ + A₂) + A₃ := by
  (expose_names; rw [add_right_associativity A₁ A₂ A₃ h h_1])

/-
This lemma shows the `Add_Left_Right_Associativity_Eqv` property `A₁ + (A₂ + A₃) = (A₁ + A₂) + A₃`.
-/
lemma add_left_right_associativity_eqv
  (A₁ A₂ A₃ : E →ₗ[𝕜] E)
  (_ : LinearMap.isPositiveSemiDefinite A₁)
  (_ : LinearMap.isPositiveSemiDefinite A₂)
  (_ : LinearMap.isPositiveSemiDefinite A₃) :
    A₁ + (A₂ + A₃) = (A₁ + A₂) + A₃ := by
  rw [add_left_associativity, add_right_associativity]; repeat assumption

/-
This lemma shows the `Zero_Prod_Identity` property `0 ⊗ A = 0`.
-/
lemma zero_prod_identity (A : E →ₗ[𝕜] E) (_: LinearMap.isPositiveSemiDefinite A) :
  TensorProduct.map (0 : F →ₗ[𝕜] F) A = 0 := by
    rw [← TensorProduct.map_zero_left A]

/-
This lemma shows the `Prod_Zero_Identity` property `A ⊗ 0 = 0`.
-/
lemma prod_zero_identity (A : E →ₗ[𝕜] E) (_: LinearMap.isPositiveSemiDefinite A) :
  TensorProduct.map A (0 : F →ₗ[𝕜] F) = 0 := by
    rw [← TensorProduct.map_zero_right A]

/-
This lemma shows the `zero_prod_prod_zero_eqv` property `0 ⊗ A = A ⊗ 0`.
-/
lemma zero_prod_prod_zero_eqv (A :  E →ₗ[𝕜] E) (_: LinearMap.isPositiveSemiDefinite A) :
  TensorProduct.map (0 : E →ₗ[𝕜] E) A  = TensorProduct.map A (0 : E →ₗ[𝕜] E) := by
    rw [prod_zero_identity, zero_prod_identity]
    repeat assumption

end AlgebraicProperties

