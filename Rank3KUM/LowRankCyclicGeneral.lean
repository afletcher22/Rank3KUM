import Rank3KUM.LowRankCyclicOneTwo
import Rank3KUM.FinalInduction

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- The old rank-three cyclic-order predicate is exactly the generic one at rank three. -/
theorem cyclicBasisOrder_three_of_cyclicBasisOrder3
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E)
    (h3 : CyclicBasisOrder3 M hn σ) :
    CyclicBasisOrder M 3 hn σ := by
  intro i
  have hset :
      cyclicWindow 3 hn σ i =
        ({(σ i : α),
          (σ (cyclicIndex n hn i 1) : α),
          (σ (cyclicIndex n hn i 2) : α)} : Set α) := by
    ext x
    simp only [cyclicWindow, Set.mem_range,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [cyclicIndex_zero]
    · rintro (hx | hx | hx)
      · subst x
        exact ⟨0, by simp [cyclicIndex_zero]⟩
      · subst x
        exact ⟨1, rfl⟩
      · subst x
        exact ⟨2, rfl⟩
  rw [hset]
  exact h3 i

/-- Rank-three KUM restated in the generic cyclic-order language. -/
theorem exists_cyclicBasisOrder_of_rank_three
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder M 3 (by omega) order := by
  obtain ⟨order, horder⟩ :=
    rankThreeKUM k M hk hE hRank hEcard hDense
  exact ⟨order,
    cyclicBasisOrder_three_of_cyclicBasisOrder3
      M (by omega) order horder⟩

#print axioms Rank3KUM.cyclicBasisOrder_three_of_cyclicBasisOrder3
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_three

end

end Rank3KUM
