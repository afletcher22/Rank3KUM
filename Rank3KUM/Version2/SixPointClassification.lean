import Rank3KUM.Version2.SixPointStructural

namespace Rank3KUM.Version2

open Finset

/-- The first canonical maximal configuration: two disjoint triples covering all six points. -/
def PairPattern6 (F : Finset (Finset (Fin 6))) : Prop :=
  ∃ a b c d e f : Fin 6,
    ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6 ∧
    F = {({a, b, c} : Finset (Fin 6)), ({d, e, f} : Finset (Fin 6))}

/-- Two disjoint members of a linear triple family force the family to consist exactly of them. -/
theorem eq_pair_of_disjoint_members
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F)
    {A B : Finset (Fin 6)}
    (hAF : A ∈ F) (hBF : B ∈ F)
    (hAB : A ≠ B)
    (hdisj : Disjoint A B) :
    F = {A, B} := by
  classical
  have hAcard : A.card = 3 := hF.1 A hAF
  have hBcard : B.card = 3 := hF.1 B hBF
  have hUnionCard : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
  have hUnion : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hUnionCard
  apply Finset.Subset.antisymm
  · intro T hTF
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hTA : T = A
    · exact Or.inl hTA
    by_cases hTB : T = B
    · exact Or.inr hTB
    exfalso
    have hTAle : (T ∩ A).card ≤ 1 := hF.2 T hTF A hAF hTA
    have hTBle : (T ∩ B).card ≤ 1 := hF.2 T hTF B hBF hTB
    have hsplit : T = (T ∩ A) ∪ (T ∩ B) := by
      ext x
      have hxAB : x ∈ A ∪ B := by
        rw [hUnion]
        exact Finset.mem_univ x
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    have hTcard : T.card = 3 := hF.1 T hTF
    have hcardle : T.card ≤ (T ∩ A).card + (T ∩ B).card := by
      rw [hsplit]
      exact Finset.card_union_le
    omega
  · intro T hT
    rw [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact hAF
    · exact hBF

/-- Hence the disjoint case is, up to naming its six points, the first canonical pattern. -/
theorem pairPattern6_of_disjoint_members
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F)
    {A B : Finset (Fin 6)}
    (hAF : A ∈ F) (hBF : B ∈ F)
    (hAB : A ≠ B)
    (hdisj : Disjoint A B) :
    PairPattern6 F := by
  classical
  have hAcard : A.card = 3 := hF.1 A hAF
  have hBcard : B.card = 3 := hF.1 B hBF
  obtain ⟨a, b, c, hab, hac, hbc, hA⟩ := Finset.card_eq_three.mp hAcard
  obtain ⟨d, e, f, hde, hdf, hef, hB⟩ := Finset.card_eq_three.mp hBcard
  have hUnionCard : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
  have hSixCard : ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6 := by
    have hEq : ({a, b, c, d, e, f} : Finset (Fin 6)) = A ∪ B := by
      rw [hA, hB]
      ext x
      simp [or_assoc, or_left_comm, or_comm]
    rw [hEq, hUnionCard]
  refine ⟨a, b, c, d, e, f, hSixCard, ?_⟩
  rw [eq_pair_of_disjoint_members hF hAF hBF hAB hdisj, hA, hB]

end Rank3KUM.Version2
