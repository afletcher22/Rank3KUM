import Rank3KUM.UniformDensity
import Mathlib.Combinatorics.Matroid.Minor.Delete

namespace Rank3KUM

open Set

variable {α : Type*}

/-- A basis whose deletion preserves rank and drops the density parameter by one. -/
def DensityReducingBasis
    (M : Matroid α) (k : ℕ) (D : Set α) : Prop :=
  M.IsBase D ∧
    (Matroid.delete M D).eRank = M.eRank ∧
    UniformlyDense (Matroid.delete M D) (k - 1)

/-- The strict-density induction needs one density-reducing basis. -/
def HasDensityReducingBasis
    (M : Matroid α) (k : ℕ) : Prop :=
  ∃ D : Set α, DensityReducingBasis M k D

/-- Every nonempty proper ground-set subset satisfies the density bound strictly. -/
def StrictlyUniformlyDense
    (M : Matroid α) (k : ℕ) : Prop :=
  ∀ X : Set α, X ⊆ M.E →
    X.Nonempty → X ≠ M.E →
    X.encard < (k : ℕ∞) * M.eRk X

/--
Uniform density splits cleanly into a nonempty proper tight set or strict
density on every nonempty proper set.
-/
theorem exists_nonempty_proper_tight_or_strictlyUniformlyDense
    (M : Matroid α) (k : ℕ)
    (hDense : UniformlyDense M k) :
    (∃ X : Set α,
      Tight M k X ∧ X.Nonempty ∧ X ≠ M.E) ∨
      StrictlyUniformlyDense M k := by
  classical
  by_cases h :
      ∃ X : Set α,
        Tight M k X ∧ X.Nonempty ∧ X ≠ M.E
  · exact Or.inl h
  · right
    intro X hXE hXnonempty hXproper
    have hle :=
      hDense X hXE
    exact lt_of_le_of_ne hle fun heq =>
      h ⟨X, ⟨hXE, heq⟩,
        hXnonempty, hXproper⟩

/-- Strict density bounds every nonempty proper rank-one set by `k-1`. -/
theorem StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one
    (M : Matroid α) (k : ℕ)
    (hStrict : StrictlyUniformlyDense M k)
    {X : Set α}
    (hXE : X ⊆ M.E)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hXrank : M.eRk X = 1) :
    X.encard < (k : ℕ∞) := by
  simpa [hXrank] using
    hStrict X hXE hXnonempty hXproper

/-- Strict density bounds every nonempty proper rank-two set below `2k`. -/
theorem StrictlyUniformlyDense.encard_lt_two_mul_k_of_eRk_eq_two
    (M : Matroid α) (k : ℕ)
    (hStrict : StrictlyUniformlyDense M k)
    {X : Set α}
    (hXE : X ⊆ M.E)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E)
    (hXrank : M.eRk X = 2) :
    X.encard < ((2 * k : ℕ) : ℕ∞) := by
  have h := hStrict X hXE hXnonempty hXproper
  rw [hXrank] at h
  simpa [Nat.mul_comm] using h

#print axioms Rank3KUM.exists_nonempty_proper_tight_or_strictlyUniformlyDense
#print axioms Rank3KUM.StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one
#print axioms Rank3KUM.StrictlyUniformlyDense.encard_lt_two_mul_k_of_eRk_eq_two

end Rank3KUM
