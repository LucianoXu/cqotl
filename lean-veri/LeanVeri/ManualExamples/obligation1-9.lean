import LeanVeri.Commons
import LeanVeri.LinearMapPropositions

variable {𝕜 : Type*} [_inst : (RCLike 𝕜)]

local notation "𝕜²" => ((EuclideanSpace 𝕜) (Fin 2))

def lt (x y : ℤ) : Bool := x < y

def iAdd : ℤ → Bool → ℤ
  | x, true => x + 1
  | x, false => x

lemma obligation (b b' : Bool) (x x' i i' m : ℤ) :
    ((lt i m = true) ∧ (lt i' m = true)) ∧ (((x = x' ∧ i = i') ∧ (b = b')) ∧ (iAdd x b = iAdd x' b')) → ((lt i m = lt i' m) ∧ ((iAdd x b = iAdd x' b') ∧ (i = i'))) := by
  simp [lt]
  intro _ _ hx hi hb hadd
  rw [hx, hi, hb]
  simp
