import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

/-!
# Palomar advertised statement

This file is the small trusted statement surface for the Palomar Registry.
It intentionally imports only Mathlib and does not import the Rank3KUM proof
development. The definitions below mirror the statement-level notions used by
the project so that the advertised theorem can be audited independently of the
proof implementation.
-/

namespace Rank3KUM.Palomar

open Set

variable {α : Type*}

/-- Every ground-set subset satisfies `|X| ≤ k · r(X)`. -/
def UniformlyDense (M : Matroid α) (k : ℕ) : Prop :=
  ∀ X : Set α, X ⊆ M.E →
    X.encard ≤ (k : ℕ∞) * M.eRk X

/-- Add a natural offset to a finite cyclic index. -/
def cyclicIndex (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩

/-- A cyclic enumeration whose every three consecutive elements form a basis. -/
def CyclicBasisOrder3
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) : Prop :=
  ∀ i : Fin n,
    M.IsBase
      ({(σ i : α),
        (σ (cyclicIndex n hn i 1) : α),
        (σ (cyclicIndex n hn i 2) : α)} : Set α)

/--
The divisible rank-three Kajitani--Ueno--Miyano cyclic basis ordering theorem:
a finite uniformly dense rank-three matroid on `3k` elements, with `k > 0`,
admits a cyclic ordering of its ground set in which every three cyclically
consecutive elements form a basis.
-/
theorem rankThreeKUM
    (k : ℕ) (M : Matroid α) (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  sorry

end Rank3KUM.Palomar
