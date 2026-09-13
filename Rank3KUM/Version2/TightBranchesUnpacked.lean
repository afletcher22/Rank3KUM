import Rank3KUM.TightFlatAutomatic
import Rank3KUM.ContractInterleave
import Rank3KUM.HalfWeave.CyclicBasisOrderingDirect

namespace Rank3KUM.Version2

open Set

noncomputable section

variable {α : Type*}

/--
A cyclic adjacent-basis ordering of a rank-two restriction is the only
rank-two input needed by the rank-two tight branch.  The ordering and its
adjacency proof are passed directly rather than through an extra structure.
-/
theorem exists_cyclicBasisOrder3_of_flat_ordering
    (M : Matroid α) {X : Set α} {k : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hXflat : M.IsFlat X)
    (points : Fin k ≃ (M.E \ X : Set α))
    (rankTwoOrder : Fin k × Bool ≃ (M.restrict X).E)
    (hadj :
      ∀ p : Fin k × Bool,
        (M.restrict X).IsBase
          ({((rankTwoOrder p : (M.restrict X).E) : α),
            ((rankTwoOrder (Rank3KUM.HalfWeave.weaveNext k hk p) :
              (M.restrict X).E) : α)} : Set α)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  let pairs : Fin k × Bool ≃ X :=
    rankTwoOrder.trans (Rank3KUM.restrictGroundEquiv M X)
  have hpairs_coe (p : Fin k × Bool) :
      (pairs p : α) =
        ((rankTwoOrder p : (M.restrict X).E) : α) := by
    exact Rank3KUM.restrictGroundEquiv_trans_apply_coe
      M X rankTwoOrder p
  have hwithin (i : Fin k) :
      M.IsBasis
        ({(pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α) X := by
    apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
    rw [hpairs_coe (i, false), hpairs_coe (i, true)]
    simpa [Rank3KUM.HalfWeave.weaveNext] using
      hadj (i, false)
  have hacross (i : Fin k) :
      M.IsBasis
        ({(pairs (i, true) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α) X := by
    apply (Matroid.isBase_restrict_iff hXflat.subset_ground).mp
    rw [hpairs_coe (i, true),
      hpairs_coe (cyclicIndex k hk i 1, false)]
    simpa [Rank3KUM.HalfWeave.weaveNext,
      Rank3KUM.halfWeave_cyclicSucc_eq_cyclicIndex] using
      hadj (i, true)
  have hPX : Disjoint (M.E \ X) X :=
    Set.disjoint_sdiff_left
  have hLocal :
      CyclicBasisOrder3 M (by omega)
        (Rank3KUM.interleaveOneTwo hPX points pairs) := by
    exact
      Rank3KUM.cyclicBasisOrder3_interleaveOneTwo_of_flat_pairs
        M hk hRank hPX Set.sdiff_subset hXflat points pairs
        hwithin hacross
  have hUnion : (M.E \ X) ∪ X = M.E :=
    Set.sdiff_union_of_subset hXflat.subset_ground
  let order : Fin (3 * k) ≃ M.E :=
    (Rank3KUM.interleaveOneTwo hPX points pairs).trans
      (Equiv.setCongr hUnion)
  refine ⟨order, ?_⟩
  intro i
  have hi := hLocal i
  simpa only [order, Equiv.trans_apply,
    Equiv.setCongr_apply] using hi

/-- Direct rank-two tight-set branch consuming the rank-two existential. -/
theorem exists_cyclicBasisOrder3_of_tight_rank_two_unpacked
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 2) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXflat : M.IsFlat X :=
    tight_isFlat M k hE hDense hX
  have hXcard :
      X.encard = ((2 * k : ℕ) : ℕ∞) :=
    tight_encard_eq_two_mul_k_of_eRk_eq_two
      M k hX hXrank
  have hsum :
      X.encard + (M.E \ X).encard = M.E.encard := by
    rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
      Set.union_sdiff_cancel hX.1]
  have hComplementCard :
      (M.E \ X).encard = (k : ℕ∞) := by
    apply ENat.add_right_injective_of_ne_top
      (ENat.natCast_ne_top (2 * k))
    calc
      ((2 * k : ℕ) : ℕ∞) + (M.E \ X).encard =
          X.encard + (M.E \ X).encard := by
        rw [hXcard]
      _ = M.E.encard := hsum
      _ = ((3 * k : ℕ) : ℕ∞) := hEcard
      _ = ((2 * k : ℕ) : ℕ∞) + (k : ℕ∞) := by
        rw [← ENat.natCast_add]
        congr 1
        omega
  have hRestrictRank :
      (M.restrict X).eRank = 2 := by
    rw [Matroid.eRank_def,
      Matroid.restrict_ground_eq,
      M.restrict_eRk_eq Set.Subset.rfl, hXrank]
  have hXfinite : X.Finite :=
    hE.subset hXflat.subset_ground
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  let : Fintype X := hXfinite.fintype
  let : Fintype (M.E \ X : Set α) :=
    hComplementFinite.fintype
  let : Fintype (M.restrict X).E :=
    Fintype.ofEquiv X (Rank3KUM.restrictGroundEquiv M X).symm
  let : DecidableEq (M.restrict X).E :=
    Classical.decEq _
  have hXncard : X.ncard = 2 * k := by
    have hcast : (X.ncard : ℕ∞) =
        ((2 * k : ℕ) : ℕ∞) := by
      rw [hXfinite.cast_ncard_eq]
      exact hXcard
    exact_mod_cast hcast
  have hRestrictCard :
      Fintype.card (M.restrict X).E = 2 * k := by
    calc
      Fintype.card (M.restrict X).E =
          Fintype.card X :=
        Fintype.card_congr (Rank3KUM.restrictGroundEquiv M X)
      _ = Nat.card X := Fintype.card_eq_nat_card
      _ = X.ncard := by
        simp only [Nat.card_coe_set_eq]
      _ = 2 * k := hXncard
  have hRestrictDense : UniformlyDense (M.restrict X) k :=
    UniformlyDense.restrict M k hDense hXflat.subset_ground
  obtain ⟨rankTwoOrder, hadj⟩ :=
    Rank3KUM.HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
      (M.restrict X) k hk hRestrictCard hRestrictDense hRestrictRank
  have hComplementNcard : (M.E \ X).ncard = k := by
    have hcast : ((M.E \ X).ncard : ℕ∞) = (k : ℕ∞) := by
      rw [hComplementFinite.cast_ncard_eq]
      exact hComplementCard
    exact_mod_cast hcast
  have hComplementNatCard : Nat.card (M.E \ X : Set α) = k := by
    simpa only [Nat.card_coe_set_eq] using hComplementNcard
  let points : Fin k ≃ (M.E \ X : Set α) :=
    (Finite.equivFinOfCardEq hComplementNatCard).symm
  exact
    exists_cyclicBasisOrder3_of_flat_ordering
      M hk hRank hXflat points rankTwoOrder hadj

/--
A cyclic adjacent-basis ordering of the rank-two contraction is the only
rank-two input needed by the rank-one tight branch.  Again the data is passed
without an intermediate packaging structure.
-/
theorem exists_cyclicBasisOrder3_of_contract_ordering
    (M : Matroid α) {X : Set α} {k : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hContractRank : (Matroid.contract M X).eRank = 2)
    (hXsubset : X ⊆ M.E)
    (hXrank : M.eRk X = 1)
    (hLoopless : M.Loopless)
    (points : Fin k ≃ X)
    (rankTwoOrder : Fin k × Bool ≃ (Matroid.contract M X).E)
    (hadj :
      ∀ p : Fin k × Bool,
        (Matroid.contract M X).IsBase
          ({((rankTwoOrder p : (Matroid.contract M X).E) : α),
            ((rankTwoOrder (Rank3KUM.HalfWeave.weaveNext k hk p) :
              (Matroid.contract M X).E) : α)} : Set α)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  let pairs : Fin k × Bool ≃ (M.E \ X : Set α) :=
    rankTwoOrder.trans (Rank3KUM.contractGroundEquiv M X)
  have hpairs_coe (p : Fin k × Bool) :
      (pairs p : α) =
        ((rankTwoOrder p : (Matroid.contract M X).E) : α) := by
    exact Rank3KUM.contractGroundEquiv_trans_apply_coe
      M X rankTwoOrder p
  have hpointBasis (i : Fin k) :
      M.IsBasis ({(points i : α)} : Set α) X :=
    Rank3KUM.isBasis_singleton_of_loopless_eRk_eq_one
      M hLoopless hXsubset hXrank (points i).property
  have hwithin (i : Fin k) :
      (Matroid.contract M X).IsBase
        ({(pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α) := by
    rw [hpairs_coe (i, false), hpairs_coe (i, true)]
    simpa [Rank3KUM.HalfWeave.weaveNext] using
      hadj (i, false)
  have hacross (i : Fin k) :
      (Matroid.contract M X).IsBase
        ({(pairs (i, true) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} : Set α) := by
    rw [hpairs_coe (i, true),
      hpairs_coe (cyclicIndex k hk i 1, false)]
    simpa [Rank3KUM.HalfWeave.weaveNext,
      Rank3KUM.halfWeave_cyclicSucc_eq_cyclicIndex] using
      hadj (i, true)
  have hDisjoint : Disjoint X (M.E \ X) :=
    Set.disjoint_sdiff_right
  have hLocal :
      CyclicBasisOrder3 M (by omega)
        (Rank3KUM.interleaveOneTwo hDisjoint points pairs) := by
    apply Rank3KUM.cyclicBasisOrder3_interleaveOneTwo
      M hk hDisjoint points pairs
    · intro i
      exact
        Rank3KUM.isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank (hpointBasis i) (hwithin i)
    · intro i
      have hbase :=
        Rank3KUM.isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank
          (hpointBasis (cyclicIndex k hk i 1))
          (hwithin i)
      convert hbase using 1
      ext x
      simp [or_comm, or_left_comm]
    · intro i
      have hbase :=
        Rank3KUM.isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank
          (hpointBasis (cyclicIndex k hk i 1))
          (hacross i)
      convert hbase using 1
      ext x
      simp [or_left_comm]
  have hUnion : X ∪ (M.E \ X) = M.E :=
    Set.union_sdiff_cancel hXsubset
  let order : Fin (3 * k) ≃ M.E :=
    (Rank3KUM.interleaveOneTwo hDisjoint points pairs).trans
      (Equiv.setCongr hUnion)
  refine ⟨order, ?_⟩
  intro i
  have hi := hLocal i
  simpa only [order, Equiv.trans_apply,
    Equiv.setCongr_apply] using hi

/-- Direct rank-one tight-set branch consuming the rank-two existential. -/
theorem exists_cyclicBasisOrder3_of_tight_rank_one_unpacked
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
      (Rank3KUM.contractGroundEquiv M X).symm
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
        Fintype.card_congr (Rank3KUM.contractGroundEquiv M X)
      _ = Nat.card (M.E \ X : Set α) :=
        Fintype.card_eq_nat_card
      _ = (M.E \ X).ncard := by
        simp only [Nat.card_coe_set_eq]
      _ = 2 * k := hComplementNcard
  have hContractDense :
      UniformlyDense (Matroid.contract M X) k :=
    Rank3KUM.UniformlyDense.contract_tight_rank_one
      M k hDense hX hXrank
  have hContractRank :
      (Matroid.contract M X).eRank = 2 :=
    Rank3KUM.eRank_contract_eq_two_of_eRank_eq_three_eRk_eq_one
      M hRank hX.1 hXrank
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  obtain ⟨rankTwoOrder, hadj⟩ :=
    Rank3KUM.HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
      (Matroid.contract M X) k hk hContractCard
      hContractDense hContractRank
  have hXNatCard : Nat.card X = k := by
    simpa only [Nat.card_coe_set_eq] using hXncard
  let points : Fin k ≃ X :=
    (Finite.equivFinOfCardEq hXNatCard).symm
  exact
    exists_cyclicBasisOrder3_of_contract_ordering
      M hk hRank hContractRank hX.1 hXrank
      hLoopless points rankTwoOrder hadj

#print axioms Rank3KUM.Version2.exists_cyclicBasisOrder3_of_tight_rank_one_unpacked
#print axioms Rank3KUM.Version2.exists_cyclicBasisOrder3_of_tight_rank_two_unpacked

end

end Rank3KUM.Version2
