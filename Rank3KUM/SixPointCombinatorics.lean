import Mathlib.Tactic

namespace Rank3KUM

open Finset

/--
Eight explicit cyclic orders cover every linear family of three-subsets of a
six-element set.  This is the finite combinatorial certificate used by the
`k = 2` strict case.
-/
def SixPointGoodAlternatives
    (Bad : Finset (Fin 6) → Prop) : Prop :=
  (¬ Bad ({0, 1, 2} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 5} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 3} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 2} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 3} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 4, 5} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 4} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 3, 5} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 2} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 2, 3} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 4} : Finset (Fin 6))) ∨
  (¬ Bad ({0, 1, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({1, 3, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({3, 4, 5} : Finset (Fin 6)) ∧
      ¬ Bad ({2, 3, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 2, 4} : Finset (Fin 6)) ∧
      ¬ Bad ({0, 1, 2} : Finset (Fin 6)))

/-- The finite list of forbidden pairs defining a linear triple family on six vertices. -/
def LinearSixBad
    (Bad : Finset (Fin 6) → Prop) : Prop :=
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 1, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 4, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({1, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) ∧
  ¬ (Bad ({2, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6)))

/--
A family satisfying the explicit linearity certificate obeys one of the
eight certified cyclic-order alternatives.
-/
set_option maxHeartbeats 1000000 in
theorem sixPointGoodAlternatives_of_linear
    (Bad : Finset (Fin 6) → Prop)
    (hlinear : LinearSixBad Bad) :
    SixPointGoodAlternatives Bad := by
  unfold LinearSixBad at hlinear
  unfold SixPointGoodAlternatives
  tauto

#print axioms Rank3KUM.sixPointGoodAlternatives_of_linear

end Rank3KUM
