import Rank3KUM.BalancedGluingGeneral
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

/--
A finite uniformly dense rank-one matroid on `k` elements has a generic
cyclic basis ordering: every one-element window is a basis.
-/
theorem exists_cyclicBasisOrder_of_rank_one
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 1)
    (hEcard : M.E.encard = (k : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin k ≃ M.E,
      CyclicBasisOrder M 1 hk order := by
  have hEncard : M.E.ncard = k := by
    have hcast : (M.E.ncard : ℕ∞) = (k : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  have hNatCard : Nat.card M.E = k := by
    simpa only [Nat.card_coe_set_eq] using hEncard
  let order : Fin k ≃ M.E :=
    (Finite.equivFinOfCardEq hNatCard).symm
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  refine ⟨order, ?_⟩
  intro i
  have heNonloop : M.IsNonloop (order i : α) :=
    hLoopless.isNonloop (order i).property
  have hInd : M.Indep ({(order i : α)} : Set α) :=
    heNonloop.indep
  have hBase : M.IsBase ({(order i : α)} : Set α) := by
    have hcard : ({(order i : α)} : Set α).encard = 1 := by simp
    apply hInd.isBase_of_eRk_ge (Set.finite_singleton _)
    exact
      (hRank.trans
        (hcard.symm.trans hInd.eRk_eq_encard.symm)).le
  have hset :
      cyclicWindow 1 hk order i =
        ({(order i : α)} : Set α) := by
    ext x
    simp only [cyclicWindow, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [cyclicIndex_zero]
    · intro hx
      subst x
      exact ⟨0, by simp [cyclicIndex_zero]⟩
  rw [hset]
  exact hBase

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
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_one
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_three

end

end Rank3KUM