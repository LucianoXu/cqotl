import LeanVeri.Commons
import LeanVeri.LinearMapPropositions

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

def lt (x y : ℤ) : Bool := x < y

lemma obligation (b b' : Bool) (x x' i i' m : ℤ) :
    (((¬ ((lt i) m) ∧ ¬ ((lt i') m)) ∧ ((x = x') ∧ (i = i'))) → (x = x')) = true := by
  simp only [lt, decide_eq_true_eq, not_lt, and_imp, eq_iff_iff, iff_true]
  intro _ _ h _
  exact h
