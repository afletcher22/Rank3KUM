import Rank3KUM.TightFactorReductionGeneral

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
If the ambient rank is `s+t` and `X` has rank `s`, then contracting `X` has
rank `t`.  This is the rank bookkeeping needed to apply the generic tight-
factor reduction from ambient-rank data.
-/
theorem contract_eRank_eq_of_eRank_eq_add
    (M : Matroid α) {X : Set α} {s t : ℕ}
    (hX : X ⊆ M.E)
    (hRank : M.eRank = s + t)
    (hXrank : M.eRk X = s) :
    (Matroid.contract M X).eRank = t := by
  have hsum :
      (Matroid.contract M X).eRank + M.eRk X = M.eRank := by
    have h :=
      eRk_union_eq_contract_eRk_add
        M hX
          (show (Matroid.contract M X).E ⊆
            (Matroid.contract M X).E from Set.Subset.rfl)
    rw [(Matroid.contract M X).eRk_ground,
      Matroid.contract_ground,
      Set.sdiff_union_of_subset hX,
      M.eRk_ground] at h
    exact h.symm
  rw [hRank, hXrank] at hsum
  apply ENat.add_left_injective_of_ne_top
    (ENat.natCast_ne_top s)
  calc
    (Matroid.contract M X).eRank + (s : ℕ∞) =
        ((s + t : ℕ) : ℕ∞) := hsum
    _ = (t : ℕ∞) + (s : ℕ∞) := by
      rw [ENat.natCast_add, add_comm]

/--
Divisible rank-five KUM is solved whenever there is a tight rank-two set:
the restriction has rank two and the contraction has rank three.
-/
theorem exists_cyclicBasisOrder_of_rank_five_of_tight_rank_two
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 5)
    (hEcard : M.E.encard = ((5 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 2) :
    ∃ order : Fin (5 * k) ≃ M.E,
      CyclicBasisOrder M 5 (by omega) order := by
  have hContractRank : (Matroid.contract M X).eRank = 3 :=
    contract_eRank_eq_of_eRank_eq_add
      (M := M) (X := X) (s := 2) (t := 3)
      hX.1 (by simpa using hRank) hXrank
  have hEcard' :
      M.E.encard = (((2 + 3) * k : ℕ) : ℕ∞) := by
    simpa using hEcard
  simpa using
    (exists_cyclicBasisOrder_of_tight_of_rank_solutions
      (M := M) (X := X) (s := 2) (t := 3) (k := k)
      (by omega) (by omega) hk hE hEcard' hDense hX hXrank
      hContractRank
      (solvesDivisibleKUMAtRank_two (α := α))
      (solvesDivisibleKUMAtRank_three (α := α)))

/--
Divisible rank-five KUM is solved whenever there is a tight rank-three set:
the restriction has rank three and the contraction has rank two.
-/
theorem exists_cyclicBasisOrder_of_rank_five_of_tight_rank_three
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 5)
    (hEcard : M.E.encard = ((5 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 3) :
    ∃ order : Fin (5 * k) ≃ M.E,
      CyclicBasisOrder M 5 (by omega) order := by
  have hContractRank : (Matroid.contract M X).eRank = 2 :=
    contract_eRank_eq_of_eRank_eq_add
      (M := M) (X := X) (s := 3) (t := 2)
      hX.1 (by simpa using hRank) hXrank
  have hEcard' :
      M.E.encard = (((3 + 2) * k : ℕ) : ℕ∞) := by
    simpa using hEcard
  simpa using
    (exists_cyclicBasisOrder_of_tight_of_rank_solutions
      (M := M) (X := X) (s := 3) (t := 2) (k := k)
      (by omega) (by omega) hk hE hEcard' hDense hX hXrank
      hContractRank
      (solvesDivisibleKUMAtRank_three (α := α))
      (solvesDivisibleKUMAtRank_two (α := α)))

/-- Rank-five KUM is therefore solved for every tight set of rank two or three. -/
theorem exists_cyclicBasisOrder_of_rank_five_of_tight_rank_two_or_three
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 5)
    (hEcard : M.E.encard = ((5 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 2 ∨ M.eRk X = 3) :
    ∃ order : Fin (5 * k) ≃ M.E,
      CyclicBasisOrder M 5 (by omega) order := by
  rcases hXrank with hTwo | hThree
  · exact
      exists_cyclicBasisOrder_of_rank_five_of_tight_rank_two
        M k hk hE hRank hEcard hDense hX hTwo
  · exact
      exists_cyclicBasisOrder_of_rank_five_of_tight_rank_three
        M k hk hE hRank hEcard hDense hX hThree

/--
Divisible rank-six KUM is solved whenever there is a tight rank-three set:
both restriction and contraction have rank three.
-/
theorem exists_cyclicBasisOrder_of_rank_six_of_tight_rank_three
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 6)
    (hEcard : M.E.encard = ((6 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXrank : M.eRk X = 3) :
    ∃ order : Fin (6 * k) ≃ M.E,
      CyclicBasisOrder M 6 (by omega) order := by
  have hContractRank : (Matroid.contract M X).eRank = 3 :=
    contract_eRank_eq_of_eRank_eq_add
      (M := M) (X := X) (s := 3) (t := 3)
      hX.1 (by simpa using hRank) hXrank
  have hEcard' :
      M.E.encard = (((3 + 3) * k : ℕ) : ℕ∞) := by
    simpa using hEcard
  simpa using
    (exists_cyclicBasisOrder_of_tight_of_rank_solutions
      (M := M) (X := X) (s := 3) (t := 3) (k := k)
      (by omega) (by omega) hk hE hEcard' hDense hX hXrank
      hContractRank
      (solvesDivisibleKUMAtRank_three (α := α))
      (solvesDivisibleKUMAtRank_three (α := α)))

#print axioms Rank3KUM.contract_eRank_eq_of_eRank_eq_add
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_five_of_tight_rank_two
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_five_of_tight_rank_three
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_five_of_tight_rank_two_or_three
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_six_of_tight_rank_three

end

end Rank3KUM