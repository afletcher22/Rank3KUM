import Rank3KUM.GenericGluing
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- Enumerate `k` blocks of length `r`, with the offset varying fastest. -/
def blockPositionEquiv (r k : ℕ) :
    Fin k × Fin r ≃ Fin (r * k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm r k)).symm

/-- The position of offset `j` in block `i`. -/
def blockPosition (r k : ℕ) (i : Fin k) (j : Fin r) :
    Fin (r * k) :=
  blockPositionEquiv r k (i, j)

@[simp] theorem blockPosition_val
    (r k : ℕ) (i : Fin k) (j : Fin r) :
    (blockPosition r k i j).val = j.val + r * i.val := by
  rfl

/--
Split each block of length `s+t` into an `s`-slot left segment followed by a
`t`-slot right segment, preserving block order on both sides.
-/
def balancedBlockIndexEquiv (s t k : ℕ) :
    Fin ((s + t) * k) ≃ Fin (s * k) ⊕ Fin (t * k) :=
  (blockPositionEquiv (s + t) k).symm |>.trans
    ((Equiv.prodCongr (Equiv.refl (Fin k)) finSumFinEquiv.symm).trans
      ((Equiv.prodSumDistrib (Fin k) (Fin s) (Fin t)).trans
        (Equiv.sumCongr (blockPositionEquiv s k)
          (blockPositionEquiv t k))))

@[simp] theorem balancedBlockIndexEquiv_left
    (s t k : ℕ) (i : Fin k) (j : Fin s) :
    balancedBlockIndexEquiv s t k
        (blockPosition (s + t) k i (Fin.castAdd t j)) =
      Sum.inl (blockPosition s k i j) := by
  simp [balancedBlockIndexEquiv, blockPosition, blockPositionEquiv]

@[simp] theorem balancedBlockIndexEquiv_right
    (s t k : ℕ) (i : Fin k) (j : Fin t) :
    balancedBlockIndexEquiv s t k
        (blockPosition (s + t) k i (Fin.natAdd s j)) =
      Sum.inr (blockPosition t k i j) := by
  simp [balancedBlockIndexEquiv, blockPosition, blockPositionEquiv]

/--
Interleave two disjoint cyclic enumerations in repeated blocks consisting of
`s` left entries followed by `t` right entries.
-/
def balancedBlockOrder
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q) :
    Fin ((s + t) * k) ≃ (P ∪ Q : Set α) :=
  (balancedBlockIndexEquiv s t k).trans
    ((Equiv.sumCongr left right).trans (Equiv.Set.union hPQ).symm)

@[simp] theorem balancedBlockOrder_left
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (j : Fin s) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i (Fin.castAdd t j)) :
          (P ∪ Q : Set α)) : α) =
      (left (blockPosition s k i j) : α) := by
  simp [balancedBlockOrder]

@[simp] theorem balancedBlockOrder_right
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (j : Fin t) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i (Fin.natAdd s j)) :
          (P ∪ Q : Set α)) : α) =
      (right (blockPosition t k i j) : α) := by
  simp [balancedBlockOrder]

#print axioms Rank3KUM.balancedBlockOrder_left
#print axioms Rank3KUM.balancedBlockOrder_right

end

end Rank3KUM
