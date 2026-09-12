import Rank3KUM.FinalInduction

/-!
# Palomar proved solution

This file presents the same statement surface as `Challenge.lean`, but proves
the advertised theorem from the full Rank3KUM development.
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
The divisible rank-three Kajitani--Ueno--Miyano cyclic basis ordering theorem.
-/
theorem rankThreeKUM
    (k : ℕ) (M : Matroid α) (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hDense' : Rank3KUM.UniformlyDense M k := by
    simpa [UniformlyDense, Rank3KUM.UniformlyDense] using hDense
  have h :=
    Rank3KUM.rankThreeKUM k M hk hE hRank hEcard hDense'
  simpa [CyclicBasisOrder3, cyclicIndex,
    Rank3KUM.CyclicBasisOrder3, Rank3KUM.cyclicIndex] using h

#print axioms Rank3KUM.Palomar.rankThreeKUM

end Rank3KUM.Palomar
