import Rank3KUM.LowRankCyclicGeneral

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
`SolvesDivisibleKUMAtRank α r` packages the divisible uniformly-dense KUM
statement at a fixed positive rank `r`, for matroids on ambient type `α`.
-/
def SolvesDivisibleKUMAtRank (α : Type*) (r : ℕ) : Prop :=
  ∀ (N : Matroid α) (k : ℕ)
    (hr : 0 < r) (hk : 0 < k)
    (_hE : N.E.Finite)
    (_hRank : N.eRank = r)
    (_hEcard : N.E.encard = ((r * k : ℕ) : ℕ∞))
    (_hDense : UniformlyDense N k),
    ∃ order : Fin (r * k) ≃ N.E,
      CyclicBasisOrder N r (Nat.mul_pos hr hk) order

/-- The divisible KUM statement is solved in rank one. -/
theorem solvesDivisibleKUMAtRank_one :
    SolvesDivisibleKUMAtRank α 1 := by
  intro N k hr hk hE hRank hEcard hDense
  have hEcard' : N.E.encard = (k : ℕ∞) := by
    simpa using hEcard
  simpa [SolvesDivisibleKUMAtRank] using
    (exists_cyclicBasisOrder_of_rank_one
      N k hk hE hRank hEcard' hDense)

/-- The divisible KUM statement is solved in rank two. -/
theorem solvesDivisibleKUMAtRank_two :
    SolvesDivisibleKUMAtRank α 2 := by
  intro N k hr hk hE hRank hEcard hDense
  exact
    exists_cyclicBasisOrder_of_rank_two
      N k hk hE hRank hEcard hDense

/-- The proved rank-three theorem supplies the rank-three solver. -/
theorem solvesDivisibleKUMAtRank_three :
    SolvesDivisibleKUMAtRank α 3 := by
  intro N k hr hk hE hRank hEcard hDense
  exact
    exists_cyclicBasisOrder_of_rank_three
      N k hk hE hRank hEcard hDense

/--
Generic tight-factor reduction for divisible KUM.

If `X` is tight with rank `s`, the contraction has rank `t`, the whole ground
has balanced size `(s+t)k`, and divisible KUM is solved at ranks `s` and `t`,
then `M` is cyclically basis-orderable. Uniform density is used only to pass
the same density parameter to the two factors; the final gluing step is the
rank-independent balanced gluing theorem.
-/
theorem exists_cyclicBasisOrder_of_tight_of_rank_solutions
    (M : Matroid α) {X : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hE : M.E.Finite)
    (hEcard : M.E.encard = (((s + t) * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    (hX : Tight M k X)
    (hXrank : M.eRk X = s)
    (hContractRank : (Matroid.contract M X).eRank = t)
    (hSolveS : SolvesDivisibleKUMAtRank α s)
    (hSolveT : SolvesDivisibleKUMAtRank α t) :
    ∃ order : Fin ((s + t) * k) ≃ M.E,
      CyclicBasisOrder M (s + t)
        (Nat.mul_pos (Nat.add_pos_left hs t) hk) order := by
  have hXfinite : X.Finite := hE.subset hX.1
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  have hRestrictFinite : (Matroid.restrict M X).E.Finite := by
    simpa [Matroid.restrict_ground_eq] using hXfinite
  have hContractFinite : (Matroid.contract M X).E.Finite := by
    simpa [Matroid.contract_ground] using hComplementFinite
  have hXcard : X.encard = ((s * k : ℕ) : ℕ∞) := by
    calc
      X.encard = (k : ℕ∞) * M.eRk X := hX.2
      _ = (k : ℕ∞) * s := by rw [hXrank]
      _ = ((k * s : ℕ) : ℕ∞) :=
        (ENat.natCast_mul k s).symm
      _ = ((s * k : ℕ) : ℕ∞) := by rw [Nat.mul_comm]
  have hsum :
      X.encard + (M.E \ X).encard = M.E.encard := by
    rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
      Set.union_sdiff_cancel hX.1]
  have hComplementCard :
      (M.E \ X).encard = ((t * k : ℕ) : ℕ∞) := by
    apply ENat.add_right_injective_of_ne_top
      (ENat.natCast_ne_top (s * k))
    calc
      ((s * k : ℕ) : ℕ∞) + (M.E \ X).encard =
          X.encard + (M.E \ X).encard := by rw [hXcard]
      _ = M.E.encard := hsum
      _ = (((s + t) * k : ℕ) : ℕ∞) := hEcard
      _ = ((s * k : ℕ) : ℕ∞) + ((t * k : ℕ) : ℕ∞) := by
        rw [Nat.add_mul, ENat.natCast_add]
  have hRestrictRank : (Matroid.restrict M X).eRank = s := by
    rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
      M.restrict_eRk_eq Set.Subset.rfl, hXrank]
  have hRestrictCard :
      (Matroid.restrict M X).E.encard = ((s * k : ℕ) : ℕ∞) := by
    simpa [Matroid.restrict_ground_eq] using hXcard
  have hContractCard :
      (Matroid.contract M X).E.encard = ((t * k : ℕ) : ℕ∞) := by
    simpa [Matroid.contract_ground] using hComplementCard
  obtain ⟨hRestrictDense, hContractDense⟩ :=
    UniformlyDense.tight_factors M k hDense hX hXfinite
  obtain ⟨σS, hS⟩ :=
    hSolveS (Matroid.restrict M X) k hs hk
      hRestrictFinite hRestrictRank hRestrictCard hRestrictDense
  obtain ⟨σT, hT⟩ :=
    hSolveT (Matroid.contract M X) k ht hk
      hContractFinite hContractRank hContractCard hContractDense
  exact
    exists_cyclicBasisOrder_of_balanced_restrict_contract
      (M := M) (X := X) (s := s) (t := t) (k := k)
      hs ht hk hX.1 σS σT hS hT

#print axioms Rank3KUM.solvesDivisibleKUMAtRank_one
#print axioms Rank3KUM.solvesDivisibleKUMAtRank_two
#print axioms Rank3KUM.solvesDivisibleKUMAtRank_three
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_tight_of_rank_solutions

end

end Rank3KUM