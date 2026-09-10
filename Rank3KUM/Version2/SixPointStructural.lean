import Rank3KUM.SixPointCombinatorics
import Mathlib.Tactic

namespace Rank3KUM.Version2

open Finset

/-- A finite family of triples on `Fin 6` is linear when distinct members meet in at most one point. -/
def LinearTripleFamily6 (F : Finset (Finset (Fin 6))) : Prop :=
  (∀ T ∈ F, T.card = 3) ∧
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≤ 1

/-- The number of members of `F` containing a point `v`. -/
def pointDegree6 (F : Finset (Finset (Fin 6))) (v : Fin 6) : ℕ :=
  (F.filter fun T => v ∈ T).card

/-- In a linear triple family on six points, a point belongs to at most two triples. -/
theorem pointDegree6_le_two
    (F : Finset (Finset (Fin 6)))
    (hF : LinearTripleFamily6 F)
    (v : Fin 6) :
    pointDegree6 F v ≤ 2 := by
  classical
  let G := F.filter fun T => v ∈ T
  let rest : Finset (Fin 6) → Finset (Fin 6) := fun T => T.erase v

  have hGsub : G ⊆ F := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hv_mem (T : Finset (Fin 6)) (hT : T ∈ G) : v ∈ T := by
    exact (Finset.mem_filter.mp hT).2
  have hrest_card (T : Finset (Fin 6)) (hT : T ∈ G) : (rest T).card = 2 := by
    have hTcard : T.card = 3 := hF.1 T (hGsub hT)
    have hvT := hv_mem T hT
    dsimp [rest]
    rw [Finset.card_erase_of_mem hvT, hTcard]
    omega

  have hpair : (G : Set (Finset (Fin 6))).PairwiseDisjoint rest := by
    intro A hAG B hBG hAB
    apply Finset.disjoint_left.2
    intro w hwA hwB
    have hwA' : w ∈ A := Finset.mem_of_mem_erase hwA
    have hwB' : w ∈ B := Finset.mem_of_mem_erase hwB
    have hwv : w ≠ v := Finset.ne_of_mem_erase hwA
    have hvA : v ∈ A := hv_mem A hAG
    have hvB : v ∈ B := hv_mem B hBG
    have hpairSub : ({v, w} : Finset (Fin 6)) ⊆ A ∩ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hvA, hvB⟩
      · exact Finset.mem_inter.mpr ⟨hwA', hwB'⟩
    have hge : 2 ≤ (A ∩ B).card := by
      have hcardle := Finset.card_le_card hpairSub
      simpa [hwv.symm] using hcardle
    have hle : (A ∩ B).card ≤ 1 :=
      hF.2 A (hGsub hAG) B (hGsub hBG) hAB
    omega

  have hUnionSub : G.biUnion rest ⊆ Finset.univ.erase v := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨T, hTG, hwT⟩
    have hwv : w ≠ v := Finset.ne_of_mem_erase hwT
    exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩
  have hUnionCard : (G.biUnion rest).card = 2 * G.card := by
    rw [Finset.card_biUnion hpair]
    calc
      (∑ T ∈ G, (rest T).card) = ∑ _T ∈ G, 2 := by
        apply Finset.sum_congr rfl
        intro T hT
        exact hrest_card T hT
      _ = 2 * G.card := by simp [Nat.mul_comm]
  have hUnivEraseCard : (Finset.univ.erase v).card = 5 := by simp
  have hle5 : 2 * G.card ≤ 5 := by
    rw [← hUnionCard, ← hUnivEraseCard]
    exact Finset.card_le_card hUnionSub
  change G.card ≤ 2
  omega

/-- Double-counting incidences: the sum of point degrees is three times the family size. -/
theorem sum_pointDegree6
    (F : Finset (Finset (Fin 6)))
    (htriples : ∀ T ∈ F, T.card = 3) :
    (∑ v : Fin 6, pointDegree6 F v) = 3 * F.card := by
  classical
  unfold pointDegree6
  calc
    (∑ v : Fin 6, (F.filter fun T => v ∈ T).card)
        = ∑ v : Fin 6, ∑ T ∈ F, if v ∈ T then 1 else 0 := by
            congr 1
            funext v
            rw [Finset.card_eq_sum_ones]
            simp only [Finset.sum_filter]
    _ = ∑ T ∈ F, ∑ v : Fin 6, if v ∈ T then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ F, T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          simpa using (Finset.sum_boole (R := ℕ) (fun v : Fin 6 => v ∈ T) Finset.univ)
    _ = ∑ _T ∈ F, 3 := by
          apply Finset.sum_congr rfl
          intro T hT
          exact htriples T hT
    _ = 3 * F.card := by simp [Nat.mul_comm]

/-- A linear family of triples on six points has at most four members. -/
theorem card_linearTripleFamily6_le_four
    (F : Finset (Finset (Fin 6)))
    (hF : LinearTripleFamily6 F) :
    F.card ≤ 4 := by
  have hdeg : ∀ v : Fin 6, pointDegree6 F v ≤ 2 :=
    pointDegree6_le_two F hF
  have hsumle : (∑ v : Fin 6, pointDegree6 F v) ≤ 12 := by
    calc
      (∑ v : Fin 6, pointDegree6 F v) ≤ ∑ _v : Fin 6, 2 :=
        Finset.sum_le_sum fun v _ => hdeg v
      _ = 12 := by norm_num
  rw [sum_pointDegree6 F hF.1] at hsumle
  omega

end Rank3KUM.Version2
