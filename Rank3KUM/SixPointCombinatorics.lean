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

/-- The eight concrete permutations certified by `SixPointGoodAlternatives`. -/
def sixPointPerm1 : Equiv.Perm (Fin 6) :=
  Equiv.refl (Fin 6)

def sixPointPerm2 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 2, 4, 1, 5, 3] : Fin 6 → Fin 6) (by decide)

def sixPointPerm3 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 1, 2, 5, 4, 3] : Fin 6 → Fin 6) (by decide)

def sixPointPerm4 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 4, 1, 3, 2, 5] : Fin 6 → Fin 6) (by decide)

def sixPointPerm5 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 1, 5, 3, 2, 4] : Fin 6 → Fin 6) (by decide)

def sixPointPerm6 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 3, 1, 4, 2, 5] : Fin 6 → Fin 6) (by decide)

def sixPointPerm7 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 2, 1, 3, 5, 4] : Fin 6 → Fin 6) (by decide)

def sixPointPerm8 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (![0, 1, 5, 3, 4, 2] : Fin 6 → Fin 6) (by decide)

/-- The propositional core of the six-point certificate. -/
private theorem sixPointSAT
    (p012 p013 p014 p015 p023 p024 p025 p034 p035 p045 p123 p124 p125 p134 p135 p145 p234 p235 p245 p345 : Prop)
    (hlinear :
      ¬ (p012 ∧ p013) ∧
      ¬ (p012 ∧ p014) ∧
      ¬ (p012 ∧ p015) ∧
      ¬ (p012 ∧ p023) ∧
      ¬ (p012 ∧ p024) ∧
      ¬ (p012 ∧ p025) ∧
      ¬ (p012 ∧ p123) ∧
      ¬ (p012 ∧ p124) ∧
      ¬ (p012 ∧ p125) ∧
      ¬ (p013 ∧ p014) ∧
      ¬ (p013 ∧ p015) ∧
      ¬ (p013 ∧ p023) ∧
      ¬ (p013 ∧ p034) ∧
      ¬ (p013 ∧ p035) ∧
      ¬ (p013 ∧ p123) ∧
      ¬ (p013 ∧ p134) ∧
      ¬ (p013 ∧ p135) ∧
      ¬ (p014 ∧ p015) ∧
      ¬ (p014 ∧ p024) ∧
      ¬ (p014 ∧ p034) ∧
      ¬ (p014 ∧ p045) ∧
      ¬ (p014 ∧ p124) ∧
      ¬ (p014 ∧ p134) ∧
      ¬ (p014 ∧ p145) ∧
      ¬ (p015 ∧ p025) ∧
      ¬ (p015 ∧ p035) ∧
      ¬ (p015 ∧ p045) ∧
      ¬ (p015 ∧ p125) ∧
      ¬ (p015 ∧ p135) ∧
      ¬ (p015 ∧ p145) ∧
      ¬ (p023 ∧ p024) ∧
      ¬ (p023 ∧ p025) ∧
      ¬ (p023 ∧ p034) ∧
      ¬ (p023 ∧ p035) ∧
      ¬ (p023 ∧ p123) ∧
      ¬ (p023 ∧ p234) ∧
      ¬ (p023 ∧ p235) ∧
      ¬ (p024 ∧ p025) ∧
      ¬ (p024 ∧ p034) ∧
      ¬ (p024 ∧ p045) ∧
      ¬ (p024 ∧ p124) ∧
      ¬ (p024 ∧ p234) ∧
      ¬ (p024 ∧ p245) ∧
      ¬ (p025 ∧ p035) ∧
      ¬ (p025 ∧ p045) ∧
      ¬ (p025 ∧ p125) ∧
      ¬ (p025 ∧ p235) ∧
      ¬ (p025 ∧ p245) ∧
      ¬ (p034 ∧ p035) ∧
      ¬ (p034 ∧ p045) ∧
      ¬ (p034 ∧ p134) ∧
      ¬ (p034 ∧ p234) ∧
      ¬ (p034 ∧ p345) ∧
      ¬ (p035 ∧ p045) ∧
      ¬ (p035 ∧ p135) ∧
      ¬ (p035 ∧ p235) ∧
      ¬ (p035 ∧ p345) ∧
      ¬ (p045 ∧ p145) ∧
      ¬ (p045 ∧ p245) ∧
      ¬ (p045 ∧ p345) ∧
      ¬ (p123 ∧ p124) ∧
      ¬ (p123 ∧ p125) ∧
      ¬ (p123 ∧ p134) ∧
      ¬ (p123 ∧ p135) ∧
      ¬ (p123 ∧ p234) ∧
      ¬ (p123 ∧ p235) ∧
      ¬ (p124 ∧ p125) ∧
      ¬ (p124 ∧ p134) ∧
      ¬ (p124 ∧ p145) ∧
      ¬ (p124 ∧ p234) ∧
      ¬ (p124 ∧ p245) ∧
      ¬ (p125 ∧ p135) ∧
      ¬ (p125 ∧ p145) ∧
      ¬ (p125 ∧ p235) ∧
      ¬ (p125 ∧ p245) ∧
      ¬ (p134 ∧ p135) ∧
      ¬ (p134 ∧ p145) ∧
      ¬ (p134 ∧ p234) ∧
      ¬ (p134 ∧ p345) ∧
      ¬ (p135 ∧ p145) ∧
      ¬ (p135 ∧ p235) ∧
      ¬ (p135 ∧ p345) ∧
      ¬ (p145 ∧ p245) ∧
      ¬ (p145 ∧ p345) ∧
      ¬ (p234 ∧ p235) ∧
      ¬ (p234 ∧ p245) ∧
      ¬ (p234 ∧ p345) ∧
      ¬ (p235 ∧ p245) ∧
      ¬ (p235 ∧ p345) ∧
      ¬ (p245 ∧ p345)) :
    (¬ p012 ∧ ¬ p123 ∧ ¬ p234 ∧ ¬ p345 ∧ ¬ p045 ∧ ¬ p015) ∨
    (¬ p024 ∧ ¬ p124 ∧ ¬ p145 ∧ ¬ p135 ∧ ¬ p035 ∧ ¬ p023) ∨
    (¬ p012 ∧ ¬ p125 ∧ ¬ p245 ∧ ¬ p345 ∧ ¬ p034 ∧ ¬ p013) ∨
    (¬ p014 ∧ ¬ p134 ∧ ¬ p123 ∧ ¬ p235 ∧ ¬ p025 ∧ ¬ p045) ∨
    (¬ p015 ∧ ¬ p135 ∧ ¬ p235 ∧ ¬ p234 ∧ ¬ p024 ∧ ¬ p014) ∨
    (¬ p013 ∧ ¬ p134 ∧ ¬ p124 ∧ ¬ p245 ∧ ¬ p025 ∧ ¬ p035) ∨
    (¬ p012 ∧ ¬ p123 ∧ ¬ p135 ∧ ¬ p345 ∧ ¬ p045 ∧ ¬ p024) ∨
    (¬ p015 ∧ ¬ p135 ∧ ¬ p345 ∧ ¬ p234 ∧ ¬ p024 ∧ ¬ p012) := by
  tauto

/--
A family satisfying the explicit linearity certificate obeys one of the
eight certified cyclic-order alternatives.
-/
theorem sixPointGoodAlternatives_of_linear
    (Bad : Finset (Fin 6) → Prop)
    (hlinear : LinearSixBad Bad) :
    SixPointGoodAlternatives Bad := by
  unfold LinearSixBad at hlinear
  unfold SixPointGoodAlternatives
  exact
    sixPointSAT
      (Bad ({0, 1, 2} : Finset (Fin 6)))
      (Bad ({0, 1, 3} : Finset (Fin 6)))
      (Bad ({0, 1, 4} : Finset (Fin 6)))
      (Bad ({0, 1, 5} : Finset (Fin 6)))
      (Bad ({0, 2, 3} : Finset (Fin 6)))
      (Bad ({0, 2, 4} : Finset (Fin 6)))
      (Bad ({0, 2, 5} : Finset (Fin 6)))
      (Bad ({0, 3, 4} : Finset (Fin 6)))
      (Bad ({0, 3, 5} : Finset (Fin 6)))
      (Bad ({0, 4, 5} : Finset (Fin 6)))
      (Bad ({1, 2, 3} : Finset (Fin 6)))
      (Bad ({1, 2, 4} : Finset (Fin 6)))
      (Bad ({1, 2, 5} : Finset (Fin 6)))
      (Bad ({1, 3, 4} : Finset (Fin 6)))
      (Bad ({1, 3, 5} : Finset (Fin 6)))
      (Bad ({1, 4, 5} : Finset (Fin 6)))
      (Bad ({2, 3, 4} : Finset (Fin 6)))
      (Bad ({2, 3, 5} : Finset (Fin 6)))
      (Bad ({2, 4, 5} : Finset (Fin 6)))
      (Bad ({3, 4, 5} : Finset (Fin 6)))
      hlinear

#print axioms Rank3KUM.sixPointGoodAlternatives_of_linear

end Rank3KUM
