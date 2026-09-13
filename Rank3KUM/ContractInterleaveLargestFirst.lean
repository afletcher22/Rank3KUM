import Rank3KUM.ContractInterleave
import Rank3KUM.HalfWeave.LargestFirstDirect

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
The rank-one tight branch using the direct largest-first rank-two construction.
The contraction/interleaving mathematics is unchanged; only the rank-two
ordering constructor is weakened.
-/
theorem exists_cyclicBasisOrder3_of_tight_rank_one_largestFirst
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 1) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXcard : X.encard = (k : ℕ∞) :=
    tight_encard_eq_k_of_eRk_eq_one M k hX hXrank
  have hsum :
      X.encard + (M.E \ X).encard = M.E.encard := by
    rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
      Set.union_sdiff_cancel hX.1]
  have hComplementCard :
      (M.E \ X).encard = ((2 * k : ℕ) : ℕ∞) := by
    apply ENat.add_right_injective_of_ne_top
      (by simp : (k : ℕ∞) ≠ ⊤)
    calc
      (k : ℕ∞) + (M.E \ X).encard =
          X.encard + (M.E \ X).encard := by
        rw [hXcard]
      _ = M.E.encard := hsum
      _ = ((3 * k : ℕ) : ℕ∞) := hEcard
      _ = (k : ℕ∞) + ((2 * k : ℕ) : ℕ∞) := by
        rw [← ENat.natCast_add]
        congr 1
        omega
  have hXfinite : X.Finite :=
    hE.subset hX.1
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  let : Fintype X := hXfinite.fintype
  let : Fintype (M.E \ X : Set α) :=
    hComplementFinite.fintype
  let : Fintype (Matroid.contract M X).E :=
    Fintype.ofEquiv (M.E \ X : Set α)
      (contractGroundEquiv M X).symm
  let : DecidableEq (Matroid.contract M X).E :=
    Classical.decEq _
  have hXncard : X.ncard = k := by
    have hcast : (X.ncard : ℕ∞) = (k : ℕ∞) := by
      rw [hXfinite.cast_ncard_eq]
      exact hXcard
    exact_mod_cast hcast
  have hComplementNcard :
      (M.E \ X).ncard = 2 * k := by
    have hcast :
        ((M.E \ X).ncard : ℕ∞) =
          ((2 * k : ℕ) : ℕ∞) := by
      rw [hComplementFinite.cast_ncard_eq]
      exact hComplementCard
    exact_mod_cast hcast
  have hContractCard :
      Fintype.card (Matroid.contract M X).E = 2 * k := by
    calc
      Fintype.card (Matroid.contract M X).E =
          Fintype.card (M.E \ X : Set α) :=
        Fintype.card_congr (contractGroundEquiv M X)
      _ = Nat.card (M.E \ X : Set α) :=
        Fintype.card_eq_nat_card
      _ = (M.E \ X).ncard := by
        simp only [Nat.card_coe_set_eq]
      _ = 2 * k := hComplementNcard
  have hContractDense :
      UniformlyDense (Matroid.contract M X) k :=
    UniformlyDense.contract_tight_rank_one
      M k hDense hX hXrank
  have hContractRank :
      (Matroid.contract M X).eRank = 2 :=
    eRank_contract_eq_two_of_eRank_eq_three_eRk_eq_one
      M hRank hX.1 hXrank
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let D :=
    HalfWeave.rankTwoLargestFirstEnumerationOfUniformlyDense
      (Matroid.contract M X) k hk hContractCard
      hContractDense hContractRank
  have hXNatCard : Nat.card X = k := by
    simpa only [Nat.card_coe_set_eq] using hXncard
  let points : Fin k ≃ X :=
    (Finite.equivFinOfCardEq hXNatCard).symm
  exact
    exists_cyclicBasisOrder3_of_contract_sortedEnumeration
      M hk hRank hContractRank hX.1 hXrank
      hLoopless points D

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_tight_rank_one_largestFirst

end

end Rank3KUM
