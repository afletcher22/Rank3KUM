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

#print axioms Rank3KUM.isBase_insert_pair_of_contract_isBase_rank3

end

end Rank3KUM
