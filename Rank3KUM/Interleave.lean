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

/-- The equivalence enumerating three-position blocks. -/
def interleavePositionEquiv (k : ℕ) :
    Fin k × Fin 3 ≃ Fin (3 * k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm 3 k)).symm

/-- The position of residue `j` in the `i`th three-element block. -/
def interleavePosition (k : ℕ) (i : Fin k) (j : Fin 3) :
    Fin (3 * k) :=
  (finCongr (Nat.mul_comm 3 k)).symm
    (finProdFinEquiv (i, j))

@[simp] theorem interleavePositionEquiv_apply
    (k : ℕ) (i : Fin k) (j : Fin 3) :
    interleavePositionEquiv k (i, j) =
      interleavePosition k i j := by
  rfl

@[simp] theorem interleavePosition_val
    (k : ℕ) (i : Fin k) (j : Fin 3) :
    (interleavePosition k i j).val = j.val + 3 * i.val := by
  rfl

/--
Interleave a `k`-element set with a `2k`-element set in blocks
`point, pair₀, pair₁`.
-/
def interleaveOneTwo
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X) :
    Fin (3 * k) ≃ (P ∪ X : Set α) := by
  classical
  exact
    (finCongr (Nat.mul_comm 3 k)).trans
      (finProdFinEquiv.symm.trans
        ((finThreeInterleaveEquiv k).trans
          ((Equiv.sumCongr points pairs).trans
            (Equiv.Set.union hPX).symm)))

/-- The first residue advances to the second within its block. -/
theorem cyclicIndex_interleave_zero_one
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 0) 1 =
      interleavePosition k i 1 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two steps from the first residue reaches the third residue. -/
theorem cyclicIndex_interleave_zero_two
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 0) 2 =
      interleavePosition k i 2 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The second residue advances to the third within its block. -/
theorem cyclicIndex_interleave_one_one
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 1) 1 =
      interleavePosition k i 2 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two steps from the second residue reaches the next block's point. -/
theorem cyclicIndex_interleave_one_two
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 1) 2 =
      interleavePosition k (cyclicIndex k hk i 1) 0 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hieq : i.val + 1 = k := by omega
    have hwrap : (i.val + 1) % k = 0 := by
      rw [hieq, Nat.mod_self]
    have hnum :
        (1 : Fin 3).val + 3 * i.val + 2 = 3 * k := by
      norm_num
      omega
    rw [hnum, hwrap, Nat.mod_self]
    norm_num

/-- The third residue advances to the next block's point. -/
theorem cyclicIndex_interleave_two_one
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 2) 1 =
      interleavePosition k (cyclicIndex k hk i 1) 0 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hieq : i.val + 1 = k := by omega
    have hwrap : (i.val + 1) % k = 0 := by
      rw [hieq, Nat.mod_self]
    have hnum :
        (2 : Fin 3).val + 3 * i.val + 1 = 3 * k := by
      norm_num
      omega
    rw [hnum, hwrap, Nat.mod_self]
    norm_num

/-- Two steps from the third residue reaches the next block's first pair entry. -/
theorem cyclicIndex_interleave_two_two
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    cyclicIndex (3 * k) (by omega) (interleavePosition k i 2) 2 =
      interleavePosition k (cyclicIndex k hk i 1) 1 := by
  apply Fin.ext
  simp only [cyclicIndex_val, interleavePosition_val]
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hieq : i.val + 1 = k := by omega
    have hwrap : (i.val + 1) % k = 0 := by
      rw [hieq, Nat.mod_self]
    have hnum :
        (2 : Fin 3).val + 3 * i.val + 2 = 3 * k + 1 := by
      norm_num
      omega
    rw [hnum, hwrap]
    have hone_lt : 1 < 3 * k := by omega
    simp [Nat.add_mod, Nat.mod_eq_of_lt hone_lt]

@[simp] theorem interleaveOneTwo_point
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 0) : (P ∪ X : Set α)) : α) =
      (points i : α) := by
  simp [interleaveOneTwo, interleavePosition]

@[simp] theorem interleaveOneTwo_pair_false
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 1) : (P ∪ X : Set α)) : α) =
      (pairs (i, false) : α) := by
  simp [interleaveOneTwo, interleavePosition]

@[simp] theorem interleaveOneTwo_pair_true
    {P X : Set α} {k : ℕ}
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (i : Fin k) :
    ((interleaveOneTwo hPX points pairs
      (interleavePosition k i 2) : (P ∪ X : Set α)) : α) =
      (pairs (i, true) : α) := by
  simp [interleaveOneTwo, interleavePosition]

/--
If each point with its pair, each pair with the next point, and the shifted
pair-point-pair window are bases, the interleaved enumeration is cyclic.
-/
theorem cyclicBasisOrder3_interleaveOneTwo
    (M : Matroid α) {P X : Set α} {k : ℕ}
    (hk : 0 < k)
    (hPX : Disjoint P X)
    (points : Fin k ≃ P)
    (pairs : Fin k × Bool ≃ X)
    (hzero : ∀ i : Fin k,
      M.IsBase
        ({(points i : α),
          (pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α))
    (hone : ∀ i : Fin k,
      M.IsBase
        ({(pairs (i, false) : α),
          (pairs (i, true) : α),
          (points (cyclicIndex k hk i 1) : α)} : Set α))
    (htwo : ∀ i : Fin k,
      M.IsBase
        ({(pairs (i, true) : α),
          (points (cyclicIndex k hk i 1) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α)) :
    CyclicBasisOrder3 M (by omega)
      (interleaveOneTwo hPX points pairs) := by
  intro pos
  obtain ⟨⟨i, j⟩, rfl⟩ :=
    (interleavePositionEquiv k).surjective pos
  have hj :
      j = (0 : Fin 3) ∨ j = (1 : Fin 3) ∨ j = (2 : Fin 3) := by
    fin_cases j
    · left
      apply Fin.ext
      rfl
    · right
      left
      apply Fin.ext
      rfl
    · right
      right
      apply Fin.ext
      rfl
  rcases hj with rfl | rfl | rfl
  · rw [interleavePositionEquiv_apply,
      cyclicIndex_interleave_zero_one k hk i,
      cyclicIndex_interleave_zero_two k hk i]
    simpa using hzero i
  · rw [interleavePositionEquiv_apply,
      cyclicIndex_interleave_one_one k hk i,
      cyclicIndex_interleave_one_two k hk i]
    simpa using hone i
  · rw [interleavePositionEquiv_apply,
      cyclicIndex_interleave_two_one k hk i,
      cyclicIndex_interleave_two_two k hk i]
    simpa using htwo i

#print axioms Rank3KUM.cyclicBasisOrder3_interleaveOneTwo

end

end Rank3KUM
