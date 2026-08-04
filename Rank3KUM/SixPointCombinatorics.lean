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

/--
A family of bad triples in which two distinct members never share two
vertices satisfies one of the eight certified cyclic-order alternatives.
-/
theorem sixPointGoodAlternatives_of_linear
    (Bad : Finset (Fin 6) → Prop)
    (hlinear :
      ∀ A B : Finset (Fin 6), A ≠ B →
        2 ≤ (A ∩ B).card → Bad A → Bad B → False) :
    SixPointGoodAlternatives Bad := by
  have h012_013 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 3} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_014 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_015 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_023 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 3} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_024 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_025 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_123 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_124 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h012_125 :
      ¬ (Bad ({0, 1, 2} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_014 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 1, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_015 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_023 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 3} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_034 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_035 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_123 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_134 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h013_135 :
      ¬ (Bad ({0, 1, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h014_015 :
      ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 1, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h014_024 :
      ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h014_034 :
      ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h014_045 :
      ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h014_124 :
      ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h014_134 :
      ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h014_145 :
      ¬ (Bad ({0, 1, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h015_025 :
      ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h015_035 :
      ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h015_045 :
      ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h015_125 :
      ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h015_135 :
      ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h015_145 :
      ¬ (Bad ({0, 1, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h023_024 :
      ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h023_025 :
      ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h023_034 :
      ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h023_035 :
      ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h023_123 :
      ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 3} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h023_234 :
      ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h023_235 :
      ¬ (Bad ({0, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h024_025 :
      ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h024_034 :
      ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h024_045 :
      ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h024_124 :
      ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h024_234 :
      ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h024_245 :
      ¬ (Bad ({0, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h025_035 :
      ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h025_045 :
      ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h025_125 :
      ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h025_235 :
      ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h025_245 :
      ¬ (Bad ({0, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h034_035 :
      ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({0, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h034_045 :
      ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h034_134 :
      ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h034_234 :
      ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h034_345 :
      ¬ (Bad ({0, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h035_045 :
      ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({0, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h035_135 :
      ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h035_235 :
      ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h035_345 :
      ¬ (Bad ({0, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h045_145 :
      ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h045_245 :
      ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h045_345 :
      ¬ (Bad ({0, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h123_124 :
      ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h123_125 :
      ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h123_134 :
      ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h123_135 :
      ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h123_234 :
      ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h123_235 :
      ¬ (Bad ({1, 2, 3} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h124_125 :
      ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 2, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h124_134 :
      ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h124_145 :
      ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h124_234 :
      ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h124_245 :
      ¬ (Bad ({1, 2, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h125_135 :
      ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h125_145 :
      ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h125_235 :
      ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h125_245 :
      ¬ (Bad ({1, 2, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h134_135 :
      ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h134_145 :
      ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h134_234 :
      ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 4} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h134_345 :
      ¬ (Bad ({1, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h135_145 :
      ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({1, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h135_235 :
      ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h135_345 :
      ¬ (Bad ({1, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h145_245 :
      ¬ (Bad ({1, 4, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h145_345 :
      ¬ (Bad ({1, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h234_235 :
      ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 3, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h234_245 :
      ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h234_345 :
      ¬ (Bad ({2, 3, 4} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h235_245 :
      ¬ (Bad ({2, 3, 5} : Finset (Fin 6)) ∧ Bad ({2, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h235_345 :
      ¬ (Bad ({2, 3, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  have h245_345 :
      ¬ (Bad ({2, 4, 5} : Finset (Fin 6)) ∧ Bad ({3, 4, 5} : Finset (Fin 6))) := by
    rintro ⟨hA, hB⟩
    exact hlinear _ _ (by decide) (by decide) hA hB
  unfold SixPointGoodAlternatives
  tauto

#print axioms Rank3KUM.sixPointGoodAlternatives_of_linear

end Rank3KUM
