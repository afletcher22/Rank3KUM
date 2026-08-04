import Rank3KUM.TwoGap
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/--
A three-element set can be ordered with any two distinct prescribed elements
in the first and final positions.
-/
theorem exists_fin3_equiv_with_endpoints
    {D : Set α} {u w : α}
    (hcard : D.encard = 3)
    (huD : u ∈ D) (hwD : w ∈ D)
    (huw : u ≠ w) :
    ∃ d : Fin 3 ≃ D,
      (d 0 : α) = u ∧ (d 2 : α) = w := by
  classical
  have hDfinite : D.Finite :=
    Set.finite_of_encard_eq_coe hcard
  letI : Fintype D := hDfinite.fintype
  have hcardF : Fintype.card D = 3 := by
    exact_mod_cast hcard
  let base : Fin 3 ≃ D :=
    (Fintype.equivFinOfCardEq hcardF).symm
  let U : D := ⟨u, huD⟩
  let W : D := ⟨w, hwD⟩
  let first : Fin 3 ≃ D :=
    base.trans (Equiv.swap (base 0) U)
  have hfirst_zero : first 0 = U := by
    simp [first]
  have hfirst_two_ne_U : first 2 ≠ U := by
    intro h
    rw [← hfirst_zero] at h
    exact (by norm_num : (2 : Fin 3) ≠ 0) (first.injective h)
  have hWU : W ≠ U := by
    intro h
    apply huw
    exact (congrArg Subtype.val h).symm
  let result : Fin 3 ≃ D :=
    first.trans (Equiv.swap (first 2) W)
  refine ⟨result, ?_, ?_⟩
  · change ((result 0 : D) : α) = u
    have hresult_zero : result 0 = U := by
      simp [result, hfirst_zero, hfirst_two_ne_U, hWU]
    exact congrArg Subtype.val hresult_zero
  · change ((result 2 : D) : α) = w
    have hresult_two : result 2 = W := by
      simp [result]
    exact congrArg Subtype.val hresult_two

/-- The range of an ordering `Fin 3 ≃ D` is exactly its three displayed values. -/
theorem set_eq_triple_of_fin3_equiv
    {D : Set α} (d : Fin 3 ≃ D) :
    D = ({(d 0 : α), (d 1 : α), (d 2 : α)} : Set α) := by
  ext x
  constructor
  · intro hx
    let xD : D := ⟨x, hx⟩
    obtain ⟨i, hi⟩ := d.surjective xD
    have hval : (d i : α) = x :=
      congrArg Subtype.val hi
    fin_cases i <;> simp_all
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · subst x
      exact (d 0).property
    · subst x
      exact (d 1).property
    · subst x
      exact (d 2).property

/-- Distinct positions in a `Fin 3` ordering have distinct underlying values. -/
theorem fin3_equiv_coe_ne
    {D : Set α} (d : Fin 3 ≃ D) {i j : Fin 3}
    (hij : i ≠ j) :
    (d i : α) ≠ (d j : α) := by
  intro h
  apply hij
  apply d.injective
  apply Subtype.ext
  exact h

end Rank3KUM.TwoGap
