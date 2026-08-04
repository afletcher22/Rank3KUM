import Rank3KUM.CyclicOrder
import Mathlib.Tactic

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
Within each three-position block, place one point first and the two entries of
the rank-two pair second and third.
-/
def finThreeInterleaveEquiv (k : ℕ) :
    Fin k × Fin 3 ≃ Fin k ⊕ (Fin k × Bool) where
  toFun x :=
    Fin.cases (Sum.inl x.1)
      (fun j =>
        Fin.cases (Sum.inr (x.1, false))
          (fun _ => Sum.inr (x.1, true)) j)
      x.2
  invFun
    | Sum.inl i => (i, 0)
    | Sum.inr (i, false) => (i, 1)
    | Sum.inr (i, true) => (i, 2)
  left_inv := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    · rfl
    · rfl
    · fin_cases j
      rfl
  right_inv := by
    intro x
    rcases x with i | ⟨i, b⟩
    · rfl
    · cases b <;> rfl

@[simp] theorem finThreeInterleaveEquiv_zero
    (k : ℕ) (i : Fin k) :
    finThreeInterleaveEquiv k (i, 0) = Sum.inl i := by
  rfl

@[simp] theorem finThreeInterleaveEquiv_one
    (k : ℕ) (i : Fin k) :
    finThreeInterleaveEquiv k (i, 1) = Sum.inr (i, false) := by
  rfl

@[simp] theorem finThreeInterleaveEquiv_two
    (k : ℕ) (i : Fin k) :
    finThreeInterleaveEquiv k (i, 2) = Sum.inr (i, true) := by
  rfl

/-- The position of residue `j` in the `i`th three-element block. -/
def interleavePosition (k : ℕ) (i : Fin k) (j : Fin 3) :
    Fin (3 * k) :=
  (finCongr (Nat.mul_comm 3 k)).symm
    (finProdFinEquiv (i, j))

/--
Interleave a `k`-element set with a `2k`-element set in blocks
`point, pair₀, pair₁`.
-/
def interleaveOneTwo
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X) :
    Fin (3 * k) ≃ (P ∪ X : Set α) :=
  (finCongr (Nat.mul_comm 3 k)).trans
    (finProdFinEquiv.symm.trans
      ((finThreeInterleaveEquiv k).trans
        ((Equiv.sumCongr points pairs).trans
          (Equiv.Set.union hPX).symm)))

@[simp] theorem interleaveOneTwo_point
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 0) : (P ∪ X : Set α)) : α) =
      (points i : α) := by
  simp [interleaveOneTwo, interleavePosition,
    finThreeInterleaveEquiv]

@[simp] theorem interleaveOneTwo_pair_false
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 1) : (P ∪ X : Set α)) : α) =
      (pairs (i, false) : α) := by
  simp [interleaveOneTwo, interleavePosition,
    finThreeInterleaveEquiv]

@[simp] theorem interleaveOneTwo_pair_true
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 2) : (P ∪ X : Set α)) : α) =
      (pairs (i, true) : α) := by
  simp [interleaveOneTwo, interleavePosition,
    finThreeInterleaveEquiv]

end

end Rank3KUM
