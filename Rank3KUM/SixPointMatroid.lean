import Rank3KUM.StrictDensity
import Rank3KUM.SixPointCombinatorics

namespace Rank3KUM

open Set

variable {α : Type*}

/--
Strict density at parameter two makes every pair of distinct ground elements
independent.
-/
theorem pair_indep_of_strict_two
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M 2)
    {a b : α}
    (haE : a ∈ M.E)
    (hbE : b ∈ M.E)
    (hab : a ≠ b) :
    M.Indep ({a, b} : Set α) := by
  letI : M.Loopless := hLoopless
  have haIndep : M.Indep ({a} : Set α) :=
    (Matroid.isNonloop_of_loopless haE).indep
  have hbNotMem : b ∉ ({a} : Set α) := by
    simpa using hab.symm
  by_contra hPairNotIndep
  have hbClosure : b ∈ M.closure ({a} : Set α) := by
    by_contra hbNotClosure
    have hInsertIndep :
        M.Indep (insert b ({a} : Set α)) :=
      (haIndep.notMem_closure_iff_of_notMem
        hbNotMem hbE).1 hbNotClosure
    apply hPairNotIndep
    simpa [pair_comm] using hInsertIndep
  have hClosureRank :
      M.eRk (M.closure ({a} : Set α)) = 1 := by
    rw [M.eRk_closure_eq, haIndep.eRk_eq_encard]
    simp
  have hClosureFinite :
      (M.closure ({a} : Set α)).Finite :=
    hE.subset (M.closure_subset_ground _)
  have hClosureNonempty :
      (M.closure ({a} : Set α)).Nonempty :=
    ⟨a, M.mem_closure_self a haE⟩
  have hClosureProper :
      M.closure ({a} : Set α) ≠ M.E := by
    intro hEq
    have hGroundRank :
        M.eRk (M.closure ({a} : Set α)) = M.eRank := by
      rw [hEq, M.eRk_ground]
    rw [hClosureRank, hRank] at hGroundRank
    norm_num at hGroundRank
  have hClosureLt :=
    StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one
      M 2 hStrict (M.closure_subset_ground _)
      hClosureNonempty hClosureProper hClosureRank
  have hClosureNcardLt :
      (M.closure ({a} : Set α)).ncard < 2 := by
    rw [← hClosureFinite.cast_ncard_eq] at hClosureLt
    exact_mod_cast hClosureLt
  have hPairSubset :
      ({a, b} : Set α) ⊆ M.closure ({a} : Set α) := by
    intro x hx
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact M.mem_closure_self a haE
    · exact hbClosure
  have hPairCardLe :
      ({a, b} : Set α).ncard ≤
        (M.closure ({a} : Set α)).ncard :=
    Set.ncard_le_ncard hPairSubset hClosureFinite
  have hPairCard : ({a, b} : Set α).ncard = 2 := by
    rw [Set.ncard_pair hab]
  omega

#print axioms Rank3KUM.pair_indep_of_strict_two

end Rank3KUM
