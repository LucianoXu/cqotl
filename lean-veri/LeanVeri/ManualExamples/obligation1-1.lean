import LeanVeri.Commons
import LeanVeri.LinearMapPropositions

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

def lt (x y : ℤ) : Bool := x < y

lemma obligation (b': Bool)  (b : Bool) (x' : ℤ) (x : ℤ) (i' : ℤ) (i : ℤ) (m : ℤ) (n : ℤ) :
  !((x == x') ∧ (i == i')) ∨ ((((lt i) m) == ((lt i') m)) ∧ ((x == x') ∧ (i == i'))) == true := by
  simp only [beq_iff_eq, Bool.decide_and, Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, lt, decide_eq_decide, Bool.decide_iff_dist, beq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [or_iff_not_imp_left]
  intro h
  simp only [not_or, not_not] at h
  rw [h.left, h.right]
  simp
