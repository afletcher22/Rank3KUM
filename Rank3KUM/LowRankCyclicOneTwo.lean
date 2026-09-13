import Rank3KUM.BalancedGluingGeneral
import Rank3KUM.HalfWeave.CyclicBasisOrderingDirect

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- A two-element cyclic window is its start and cyclic successor. -/
theorem cyclicWindow_two_eq_pair
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow 2 hn σ i =
      ({(σ i : α),
        (σ (cyclicIndex n hn i 1) : α)} : Set α) := by
  ext x
  simp only [cyclicWindow, Set.mem_range,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · left
      simp [cyclicIndex_zero]
    · right
      rfl
  · rintro (hx | hx)
    · subst x
      exact ⟨0, by simp [cyclicIndex_zero]⟩
    · subst x
      exact ⟨1, rfl⟩

/-- Identify the two offsets in each rank-two block with the HalfWeave Boolean label. -/
def finTwoBoolEquiv : Fin 2 ≃ Bool where
  toFun i := Fin.cases false (fun _ => true) i
  invFun
    | false => 0
    | true => 1
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · fin_cases j
      rfl
  right_inv b := by
    cases b <;> rfl

/-- Numeric traversal positions `2i,2i+1` corresponding to HalfWeave states. -/
def rankTwoTraversalEquiv (k : ℕ) :
    Fin k × Bool ≃ Fin (2 * k) :=
  (Equiv.prodCongr (Equiv.refl (Fin k)) finTwoBoolEquiv.symm).trans
    (blockPositionEquiv 2 k)

@[simp] theorem rankTwoTraversalEquiv_false
    (k : ℕ) (i : Fin k) :
    rankTwoTraversalEquiv k (i, false) =
      blockPosition 2 k i 0 := by
  rfl

@[simp] theorem rankTwoTraversalEquiv_true
    (k : ℕ) (i : Fin k) :
    rankTwoTraversalEquiv k (i, true) =
      blockPosition 2 k i 1 := by
  rfl

/-- Advancing one numeric position is exactly the HalfWeave successor. -/
theorem cyclicIndex_rankTwoTraversal_succ
    (k : ℕ) (hk : 0 < k) (p : Fin k × Bool) :
    cyclicIndex (2 * k) (by omega)
        (rankTwoTraversalEquiv k p) 1 =
      rankTwoTraversalEquiv k (HalfWeave.weaveNext k hk p) := by
  rcases p with ⟨i, b⟩
  cases b
  · simp only [HalfWeave.weaveNext_false,
      rankTwoTraversalEquiv_false, rankTwoTraversalEquiv_true]
    simpa using
      (cyclicIndex_blockPosition_same
        2 k (by omega) hk i (0 : Fin 2) 1 (by omega))
  · simp only [HalfWeave.weaveNext_true,
      rankTwoTraversalEquiv_true, rankTwoTraversalEquiv_false]
    have hcross :=
      cyclicIndex_blockPosition_next
        2 k (by omega) hk i (1 : Fin 2) 1 (by omega) (by omega)
    rw [hcross]
    apply Fin.ext
    simp only [blockPosition_val]
    simp [HalfWeave.cyclicSucc_val, cyclicIndex_val]

/-- A HalfWeave adjacent-basis order is a generic cyclic basis order of rank two. -/
theorem cyclicBasisOrder_two_of_halfWeave
    (M : Matroid α) (k : ℕ) (hk : 0 < k)
    (ρ : Fin k × Bool ≃ M.E)
    (hadj : ∀ p : Fin k × Bool,
      M.IsBase
        ({((ρ p : M.E) : α),
          ((ρ (HalfWeave.weaveNext k hk p) : M.E) : α)} : Set α)) :
    ∃ order : Fin (2 * k) ≃ M.E,
      CyclicBasisOrder M 2 (by omega) order := by
  let traversal : Fin k × Bool ≃ Fin (2 * k) :=
    rankTwoTraversalEquiv k
  let order : Fin (2 * k) ≃ M.E :=
    traversal.symm.trans ρ
  refine ⟨order, ?_⟩
  intro p
  let q : Fin k × Bool := traversal.symm p
  have hp : traversal q = p := traversal.apply_symm_apply p
  rw [← hp, cyclicWindow_two_eq_pair]
  rw [cyclicIndex_rankTwoTraversal_succ k hk q]
  simpa [order, traversal, q] using hadj q

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
    ∃ order : Fin (1 * k) ≃ M.E,
      CyclicBasisOrder M 1 (Nat.mul_pos (by omega) hk) order := by
  letI : Fintype M.E := hE.fintype
  have hEncard : M.E.ncard = k := by
    have hcast : (M.E.ncard : ℕ∞) = (k : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  have hNatCard : Nat.card M.E = k := by
    simpa only [Nat.card_coe_set_eq] using hEncard
  let baseOrder : Fin k ≃ M.E :=
    (Finite.equivFinOfCardEq hNatCard).symm
  let order : Fin (1 * k) ≃ M.E :=
    (finCongr (by omega)).trans baseOrder
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let : M.Loopless := hLoopless
  refine ⟨order, ?_⟩
  intro i
  have heNonloop : M.IsNonloop (order i : α) :=
    Matroid.isNonloop_of_loopless (order i).property
  have hInd : M.Indep ({(order i : α)} : Set α) :=
    heNonloop.indep
  have hBase : M.IsBase ({(order i : α)} : Set α) := by
    have hcard : ({(order i : α)} : Set α).encard = 1 := by simp
    apply hInd.isBase_of_eRk_ge (Set.finite_singleton _)
    exact
      (hRank.trans
        (hcard.symm.trans hInd.eRk_eq_encard.symm)).le
  have hset :
      cyclicWindow 1 (Nat.mul_pos (by omega) hk) order i =
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

/-- A finite uniformly dense rank-two matroid on `2k` elements has a generic cyclic basis ordering. -/
theorem exists_cyclicBasisOrder_of_rank_two
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 2)
    (hEcard : M.E.encard = ((2 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (2 * k) ≃ M.E,
      CyclicBasisOrder M 2 (by omega) order := by
  letI : Fintype M.E := hE.fintype
  letI : DecidableEq M.E := Classical.decEq _
  have hEncard : M.E.ncard = 2 * k := by
    have hcast : (M.E.ncard : ℕ∞) = ((2 * k : ℕ) : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  have hcard : Fintype.card M.E = 2 * k := by
    calc
      Fintype.card M.E = Nat.card M.E := Fintype.card_eq_nat_card
      _ = M.E.ncard := by simp only [Nat.card_coe_set_eq]
      _ = 2 * k := hEncard
  obtain ⟨ρ, hadj⟩ :=
    HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
      M k hk hcard hDense hRank
  exact cyclicBasisOrder_two_of_halfWeave M k hk ρ hadj

#print axioms Rank3KUM.cyclicWindow_two_eq_pair
#print axioms Rank3KUM.cyclicIndex_rankTwoTraversal_succ
#print axioms Rank3KUM.cyclicBasisOrder_two_of_halfWeave
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_one
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_two

end

end Rank3KUM
