import Rank3KUM.BalancedInterleaveGeneral

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- Evaluate a balanced block position known to lie in its left segment. -/
theorem balancedBlockOrder_apply_left_of_lt
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (d : Fin (s + t))
    (hd : d.val < s) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i d) : (P ∪ Q : Set α)) : α) =
      (left (blockPosition s k i ⟨d.val, hd⟩) : α) := by
  let j : Fin s := ⟨d.val, hd⟩
  have hdEq : d = Fin.castAdd t j := by
    apply Fin.ext
    rfl
  subst d
  simpa [j] using balancedBlockOrder_left hPQ left right i j

/-- Evaluate a balanced block position known to lie in its right segment. -/
theorem balancedBlockOrder_apply_right_of_le
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (d : Fin (s + t))
    (hd : s ≤ d.val) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i d) : (P ∪ Q : Set α)) : α) =
      (right (blockPosition t k i
        ⟨d.val - s, by omega⟩) : α) := by
  let j : Fin t := ⟨d.val - s, by omega⟩
  have hdEq : d = Fin.natAdd s j := by
    apply Fin.ext
    change d.val = s + (d.val - s)
    omega
  subst d
  simpa [j] using balancedBlockOrder_right hPQ left right i j

#print axioms Rank3KUM.balancedBlockOrder_apply_left_of_lt
#print axioms Rank3KUM.balancedBlockOrder_apply_right_of_le

end

end Rank3KUM
