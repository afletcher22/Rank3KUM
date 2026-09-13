import Rank3KUM.FinalInduction
import Challenge

/-!
# Project-to-Challenge statement contract

This file is a compilation guard against drift between the substantive project definitions/theorem
and the frozen Palomar challenge surface. It contains no new mathematical theorem.
-/

namespace Rank3KUM.MeasurementContract

open Set

variable {α : Type*}

example (M : Matroid α) (k : ℕ) :
    Rank3KUM.Palomar.UniformlyDense M k = Rank3KUM.UniformlyDense M k := by
  rfl

example (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) :
    Rank3KUM.Palomar.cyclicIndex n hn i j = Rank3KUM.cyclicIndex n hn i j := by
  rfl

example (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) :
    Rank3KUM.Palomar.CyclicBasisOrder3 M hn σ =
      Rank3KUM.CyclicBasisOrder3 M hn σ := by
  rfl

example
    (k : ℕ) (M : Matroid α) (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : Rank3KUM.Palomar.UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      Rank3KUM.Palomar.CyclicBasisOrder3 M (by omega) order := by
  have hDense' : Rank3KUM.UniformlyDense M k := by
    simpa only [Rank3KUM.Palomar.UniformlyDense, Rank3KUM.UniformlyDense] using hDense
  have h := Rank3KUM.rankThreeKUM k M hk hE hRank hEcard hDense'
  simpa only [
    Rank3KUM.Palomar.CyclicBasisOrder3,
    Rank3KUM.Palomar.cyclicIndex,
    Rank3KUM.CyclicBasisOrder3,
    Rank3KUM.cyclicIndex
  ] using h

end Rank3KUM.MeasurementContract
