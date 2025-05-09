
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection

variable {𝕜 E : Type*} [RCLike 𝕜]
variable? [HilbertSpace 𝕜 E] => [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [FiniteDimensional 𝕜 E]

namespace LinearMap
/-- Positive semidefinite operators. -/
def isPositiveSemiDefinite (T : E →ₗ[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ RCLike.re (inner 𝕜 (T x) x)

end LinearMap

open scoped TensorProduct

/-
This lemma shows the `Zero_Prod_Identity` property `0 ⊗ A = 0`.
-/
lemma zero_prod_identity (A : E →ₗ[𝕜] E) (_: LinearMap.isPositiveSemiDefinite A) :
  TensorProduct.map (0) A = 0 := by sorry

/-
  It gives errors:
    typeclass instance problem is stuck, it is often due to metavariables
  Module ?m.2630 (E →ₗ[𝕜] E)
-/
