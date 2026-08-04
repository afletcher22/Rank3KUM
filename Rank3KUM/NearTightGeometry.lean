import Rank3KUM.StrictDensity

namespace Rank3KUM

open Set

variable {α : Type*}

/--
Two distinct finite rank-two flats of the same cardinality span the ambient
rank-three matroid.
-/
theorem eRk_union_eq_three_of_distinct_rankTwo_flats
    (M : Matroid α)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    {A B : Set α}
    (hAflat : M.IsFlat A)
    (hBflat : M.IsFlat B)
    (hArank : M.eRk A = 2)
    (_hBrank : M.eRk B = 2)
    (hAcard : A.ncard = B.ncard)
    (hAB : A ≠ B) :
    M.eRk (A ∪ B) = 3 := by
  have hAfin : A.Finite :=
    hE.subset hAflat.subset_ground
  have hBfin : B.Finite :=
    hE.subset hBflat.subset_ground
  have hBnotA : ¬ B ⊆ A := by
    intro hBA
    have hcardLe : A.encard ≤ B.encard := by
      rw [← hAfin.cast_ncard_eq,
        ← hBfin.cast_ncard_eq, hAcard]
    have hBAeq : B = A :=
      hBfin.eq_of_subset_of_encard_le hBA hcardLe
    exact hAB hBAeq.symm
  obtain ⟨b, hbB, hbA⟩ := Set.not_subset.mp hBnotA
  have hbE : b ∈ M.E :=
    hBflat.subset_ground hbB
  have hbNotClosure : b ∉ M.closure A := by
    rw [hAflat.closure]
    exact hbA
  have hInsertRank : M.eRk (insert b A) = 3 := by
    rw [M.eRk_insert_eq_add_one ⟨hbE, hbNotClosure⟩,
      hArank]
    norm_num
  have hInsertSubset : insert b A ⊆ A ∪ B := by
    intro x hx
    rcases hx with rfl | hxA
    · exact Or.inr hbB
    · exact Or.inl hxA
  have hLower : 3 ≤ M.eRk (A ∪ B) := by
    rw [← hInsertRank]
    exact M.eRk_mono hInsertSubset
  apply le_antisymm
  · calc
      M.eRk (A ∪ B) ≤ M.eRank :=
        M.eRk_le_eRank _
      _ = 3 := hRank
  · exact hLower

#print axioms Rank3KUM.eRk_union_eq_three_of_distinct_rankTwo_flats

end Rank3KUM
