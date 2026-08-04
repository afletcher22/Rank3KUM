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

end Rank3KUM.TwoGap
