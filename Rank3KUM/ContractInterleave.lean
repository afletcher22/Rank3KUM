import Rank3KUM.HalfWeave.ParallelClasses
import Rank3KUM.Interleave
import Mathlib.Combinatorics.Matroid.Minor.Contract

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
A basis of a contraction by a rank-one set lifts, after adjoining a singleton
basis of the contracted set, to a basis of the original rank-three matroid.
-/
theorem isBase_insert_pair_of_contract_isBase_rank3
    (M : Matroid α) {X : Set α}
    (hRank : M.eRank = 3)
    (hContractRank : (Matroid.contract M X).eRank = 2)
    {e f g : α}
    (heBasis : M.IsBasis ({e} : Set α) X)
    (hpair : (Matroid.contract M X).IsBase
      ({f, g} : Set α)) :
    M.IsBase ({e, f, g} : Set α) := by
  have hdata :=
    heBasis.contract_indep_iff.mp hpair.indep
  have hset :
      ({f, g} : Set α) ∪ ({e} : Set α) =
        ({e, f, g} : Set α) := by
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  have htriple : M.Indep ({e, f, g} : Set α) := by
    rw [hset] at hdata
    exact hdata.1
  have heX : e ∈ X :=
    heBasis.subset (by simp)
  have heNot : e ∉ ({f, g} : Set α) := by
    intro he
    exact Set.disjoint_left.1 hdata.2 heX he
  have hpaircard :
      ({f, g} : Set α).encard = 2 :=
    hpair.encard_eq_eRank.trans hContractRank
  apply htriple.isBase_of_eRk_ge
    (Set.toFinite {e, f, g})
  rw [hRank, htriple.eRk_eq_encard,
    Set.encard_insert_of_notMem heNot, hpaircard]
  norm_num

/-- Contracted ground elements are value-identical to elements of the complement. -/
def contractGroundEquiv (M : Matroid α) (X : Set α) :
    (Matroid.contract M X).E ≃ (M.E \ X : Set α) where
  toFun e := ⟨e, by simpa using e.property⟩
  invFun e := ⟨e, by simpa using e.property⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

@[simp] theorem contractGroundEquiv_trans_apply_coe
    {β : Type*} (M : Matroid α) (X : Set α)
    (σ : β ≃ (Matroid.contract M X).E) (x : β) :
    (((σ.trans (contractGroundEquiv M X)) x :
      (M.E \ X : Set α)) : α) =
      ((σ x : (Matroid.contract M X).E) : α) := by
  rfl

/-- Every point of a loopless rank-one set is a singleton basis of that set. -/
theorem isBasis_singleton_of_loopless_eRk_eq_one
    (M : Matroid α)
    (hLoopless : M.Loopless)
    {X : Set α}
    (hXsubset : X ⊆ M.E)
    (hXrank : M.eRk X = 1)
    {e : α}
    (heX : e ∈ X) :
    M.IsBasis ({e} : Set α) X := by
  letI : M.Loopless := hLoopless
  have heNonloop : M.IsNonloop e :=
    Matroid.isNonloop_of_loopless (hXsubset heX)
  exact
    (heNonloop.indep.isBasis'_of_eRk_ge
      (by simp)
      (by simpa using heX)
      (by rw [hXrank, heNonloop.eRk_eq])).isBasis

/--
A sorted rank-two enumeration of the contraction by a rank-one set interleaves
with any enumeration of that set to give a cyclic rank-three basis order.
-/
theorem exists_cyclicBasisOrder3_of_contract_sortedEnumeration
    (M : Matroid α) {X : Set α} {k m : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hContractRank : (Matroid.contract M X).eRank = 2)
    (hXsubset : X ⊆ M.E)
    (hXrank : M.eRk X = 1)
    (hLoopless : M.Loopless)
    (points : Fin k ≃ X)
    (D : HalfWeave.RankTwoSortedEnumeration
      (Matroid.contract M X) k m) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  let pairs : Fin k × Bool ≃ (M.E \ X : Set α) :=
    (HalfWeave.rankTwoWoven D hk).trans
      (contractGroundEquiv M X)
  have hpairs_coe (p : Fin k × Bool) :
      (pairs p : α) =
        ((HalfWeave.rankTwoWoven D hk p :
          (Matroid.contract M X).E) : α) := by
    exact contractGroundEquiv_trans_apply_coe
      M X (HalfWeave.rankTwoWoven D hk) p
  have hpointBasis (i : Fin k) :
      M.IsBasis ({(points i : α)} : Set α) X :=
    isBasis_singleton_of_loopless_eRk_eq_one
      M hLoopless hXsubset hXrank (points i).property
  have hwithin (i : Fin k) :
      (Matroid.contract M X).IsBase
        ({(pairs (i, false) : α),
          (pairs (i, true) : α)} : Set α) := by
    rw [hpairs_coe (i, false), hpairs_coe (i, true)]
    simpa using
      (HalfWeave.rankTwoWoven_successor_isBase
        (Matroid.contract M X) D hk hContractRank
        (i, false))
  have hacross (i : Fin k) :
      (Matroid.contract M X).IsBase
        ({(pairs (i, true) : α),
          (pairs (cyclicIndex k hk i 1, false) : α)} :
            Set α) := by
    rw [hpairs_coe (i, true),
      hpairs_coe (cyclicIndex k hk i 1, false)]
    simpa [halfWeave_cyclicSucc_eq_cyclicIndex] using
      (HalfWeave.rankTwoWoven_successor_isBase
        (Matroid.contract M X) D hk hContractRank
        (i, true))
  have hDisjoint : Disjoint X (M.E \ X) :=
    Set.disjoint_sdiff_right
  have hLocal :
      CyclicBasisOrder3 M (by omega)
        (interleaveOneTwo hDisjoint points pairs) := by
    apply cyclicBasisOrder3_interleaveOneTwo
      M hk hDisjoint points pairs
    · intro i
      exact
        isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank (hpointBasis i) (hwithin i)
    · intro i
      have hbase :=
        isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank
          (hpointBasis (cyclicIndex k hk i 1))
          (hwithin i)
      convert hbase using 1
      ext x
      simp [or_comm, or_left_comm, or_assoc]
    · intro i
      have hbase :=
        isBase_insert_pair_of_contract_isBase_rank3
          M hRank hContractRank
          (hpointBasis (cyclicIndex k hk i 1))
          (hacross i)
      convert hbase using 1
      ext x
      simp [or_comm, or_left_comm, or_assoc]
  have hUnion : X ∪ (M.E \ X) = M.E :=
    Set.union_sdiff_cancel hXsubset
  let order : Fin (3 * k) ≃ M.E :=
    (interleaveOneTwo hDisjoint points pairs).trans
      (Equiv.setCongr hUnion)
  refine ⟨order, ?_⟩
  intro i
  have hi := hLocal i
  simpa only [order, Equiv.trans_apply,
    Equiv.setCongr_apply] using hi

#print axioms Rank3KUM.isBase_insert_pair_of_contract_isBase_rank3
#print axioms Rank3KUM.contractGroundEquiv_trans_apply_coe
#print axioms Rank3KUM.isBasis_singleton_of_loopless_eRk_eq_one
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_contract_sortedEnumeration

end

end Rank3KUM
