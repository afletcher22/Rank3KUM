import Rank3KUM.LowRankCyclicGeneral
import Rank3KUM.StrictDensity

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- A nonempty proper tight set in the divisible rank-four setting has rank 1, 2, or 3. -/
theorem tight_rank_one_or_two_or_three_rank_four
    (M : Matroid α) (k : ℕ)
    (hE : M.E.Finite)
    (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((4 * k : ℕ) : ℕ∞))
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    M.eRk X = 1 ∨ M.eRk X = 2 ∨ M.eRk X = 3 := by
  have hXfinite : X.Finite := hE.subset hX.1
  have hr_ne_zero : M.eRk X ≠ 0 := by
    intro hr_zero
    have hencard_zero : X.encard = 0 := by
      rw [hX.2, hr_zero]
      simp
    exact hXnonempty.ne_empty
      (Set.encard_eq_zero.mp hencard_zero)
  have hr_ne_four : M.eRk X ≠ 4 := by
    intro hr_four
    have hcard_eq : X.encard = M.E.encard := by
      calc
        X.encard = (k : ℕ∞) * M.eRk X := hX.2
        _ = (k : ℕ∞) * 4 := by rw [hr_four]
        _ = ((k * 4 : ℕ) : ℕ∞) :=
          (ENat.natCast_mul k 4).symm
        _ = ((4 * k : ℕ) : ℕ∞) := by rw [Nat.mul_comm]
        _ = M.E.encard := hEcard.symm
    have hXE : X = M.E :=
      hXfinite.eq_of_subset_of_encard_le
        hX.1 hcard_eq.symm.le
    exact hXproper hXE
  have hr_le_four : M.eRk X ≤ 4 := by
    calc
      M.eRk X ≤ M.eRank := M.eRk_le_eRank X
      _ = 4 := hRank
  obtain ⟨n, hr_eq, hn⟩ := ENat.le_natCast_iff.mp hr_le_four
  rw [hr_eq] at hr_ne_zero hr_ne_four ⊢
  interval_cases n <;> simp_all

/-- A tight rank-three set has cardinality `3k`. -/
theorem tight_encard_eq_three_mul_k_of_eRk_eq_three
    (M : Matroid α) (k : ℕ)
    {X : Set α}
    (hX : Tight M k X)
    (hr : M.eRk X = 3) :
    X.encard = ((3 * k : ℕ) : ℕ∞) := by
  calc
    X.encard = (k : ℕ∞) * M.eRk X := hX.2
    _ = (k : ℕ∞) * 3 := by rw [hr]
    _ = ((k * 3 : ℕ) : ℕ∞) :=
      (ENat.natCast_mul k 3).symm
    _ = ((3 * k : ℕ) : ℕ∞) := by rw [Nat.mul_comm]

/-- Contracting `X` subtracts its rank from the ambient rank. -/
theorem eRank_contract_add_eRk_eq_eRank
    (M : Matroid α) {X : Set α}
    (hX : X ⊆ M.E) :
    (Matroid.contract M X).eRank + M.eRk X = M.eRank := by
  have hrank :=
    eRk_union_eq_contract_eRk_add
      M hX
        (show (Matroid.contract M X).E ⊆
          (Matroid.contract M X).E from Set.Subset.rfl)
  rw [(Matroid.contract M X).eRk_ground,
    Matroid.contract_ground,
    Set.sdiff_union_of_subset hX,
    M.eRk_ground] at hrank
  exact hrank.symm

/-- In rank four, contracting a rank-one set leaves rank three. -/
theorem eRank_contract_eq_three_of_eRank_eq_four_eRk_eq_one
    (M : Matroid α)
    (hRank : M.eRank = 4)
    {X : Set α}
    (hX : X ⊆ M.E)
    (hXrank : M.eRk X = 1) :
    (Matroid.contract M X).eRank = 3 := by
  have h := eRank_contract_add_eRk_eq_eRank M hX
  rw [hRank, hXrank] at h
  apply ENat.add_left_injective_of_ne_top
    (by simp : (1 : ℕ∞) ≠ ⊤)
  calc
    (Matroid.contract M X).eRank + 1 = 4 := h
    _ = (3 : ℕ∞) + 1 := by norm_num

/-- In rank four, contracting a rank-two set leaves rank two. -/
theorem eRank_contract_eq_two_of_eRank_eq_four_eRk_eq_two
    (M : Matroid α)
    (hRank : M.eRank = 4)
    {X : Set α}
    (hX : X ⊆ M.E)
    (hXrank : M.eRk X = 2) :
    (Matroid.contract M X).eRank = 2 := by
  have h := eRank_contract_add_eRk_eq_eRank M hX
  rw [hRank, hXrank] at h
  apply ENat.add_left_injective_of_ne_top
    (by simp : (2 : ℕ∞) ≠ ⊤)
  calc
    (Matroid.contract M X).eRank + 2 = 4 := h
    _ = (2 : ℕ∞) + 2 := by norm_num

/-- In rank four, contracting a rank-three set leaves rank one. -/
theorem eRank_contract_eq_one_of_eRank_eq_four_eRk_eq_three
    (M : Matroid α)
    (hRank : M.eRank = 4)
    {X : Set α}
    (hX : X ⊆ M.E)
    (hXrank : M.eRk X = 3) :
    (Matroid.contract M X).eRank = 1 := by
  have h := eRank_contract_add_eRk_eq_eRank M hX
  rw [hRank, hXrank] at h
  apply ENat.add_left_injective_of_ne_top
    (by simp : (3 : ℕ∞) ≠ ⊤)
  calc
    (Matroid.contract M X).eRank + 3 = 4 := h
    _ = (1 : ℕ∞) + 3 := by norm_num

/--
Every nonempty proper tight-set case of divisible rank-four KUM reduces to
rank-one, rank-two, and rank-three factors and is therefore cyclically
basis-orderable.
-/
theorem exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((4 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ order : Fin (4 * k) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) order := by
  have hXfinite : X.Finite := hE.subset hX.1
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  have hRestrictFinite : (Matroid.restrict M X).E.Finite := by
    simpa [Matroid.restrict_ground_eq] using hXfinite
  have hContractFinite : (Matroid.contract M X).E.Finite := by
    simpa [Matroid.contract_ground] using hComplementFinite
  obtain ⟨hRestrictDense, hContractDense⟩ :=
    UniformlyDense.tight_factors M k hDense hX hXfinite
  rcases tight_rank_one_or_two_or_three_rank_four
      M k hE hRank hEcard hX hXnonempty hXproper with
    hOne | hTwo | hThree
  · have hXcard : X.encard = (k : ℕ∞) :=
      tight_encard_eq_k_of_eRk_eq_one M k hX hOne
    have hsum :
        X.encard + (M.E \ X).encard = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hX.1]
    have hComplementCard :
        (M.E \ X).encard = ((3 * k : ℕ) : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top
        (by simp : (k : ℕ∞) ≠ ⊤)
      calc
        (k : ℕ∞) + (M.E \ X).encard =
            X.encard + (M.E \ X).encard := by rw [hXcard]
        _ = M.E.encard := hsum
        _ = ((4 * k : ℕ) : ℕ∞) := hEcard
        _ = (k : ℕ∞) + ((3 * k : ℕ) : ℕ∞) := by
          rw [← ENat.natCast_add]
          congr 1
          omega
    have hRestrictRank : (Matroid.restrict M X).eRank = 1 := by
      rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
        M.restrict_eRk_eq Set.Subset.rfl, hOne]
    have hContractRank : (Matroid.contract M X).eRank = 3 :=
      eRank_contract_eq_three_of_eRank_eq_four_eRk_eq_one
        M hRank hX.1 hOne
    have hRestrictCard :
        (Matroid.restrict M X).E.encard = (k : ℕ∞) := by
      simpa [Matroid.restrict_ground_eq] using hXcard
    have hContractCard :
        (Matroid.contract M X).E.encard = ((3 * k : ℕ) : ℕ∞) := by
      simpa [Matroid.contract_ground] using hComplementCard
    obtain ⟨σS, hS⟩ :=
      exists_cyclicBasisOrder_of_rank_one
        (Matroid.restrict M X) k hk hRestrictFinite
        hRestrictRank hRestrictCard hRestrictDense
    obtain ⟨σT, hT⟩ :=
      exists_cyclicBasisOrder_of_rank_three
        (Matroid.contract M X) k hk hContractFinite
        hContractRank hContractCard hContractDense
    simpa using
      (exists_cyclicBasisOrder_of_balanced_restrict_contract
        (M := M) (X := X) (s := 1) (t := 3) (k := k)
        (by omega) (by omega) hk hX.1 σS σT hS hT)
  · have hXcard : X.encard = ((2 * k : ℕ) : ℕ∞) :=
      tight_encard_eq_two_mul_k_of_eRk_eq_two M k hX hTwo
    have hsum :
        X.encard + (M.E \ X).encard = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hX.1]
    have hComplementCard :
        (M.E \ X).encard = ((2 * k : ℕ) : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top
        (ENat.natCast_ne_top (2 * k))
      calc
        ((2 * k : ℕ) : ℕ∞) + (M.E \ X).encard =
            X.encard + (M.E \ X).encard := by rw [hXcard]
        _ = M.E.encard := hsum
        _ = ((4 * k : ℕ) : ℕ∞) := hEcard
        _ = ((2 * k : ℕ) : ℕ∞) + ((2 * k : ℕ) : ℕ∞) := by
          rw [← ENat.natCast_add]
          congr 1
          omega
    have hRestrictRank : (Matroid.restrict M X).eRank = 2 := by
      rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
        M.restrict_eRk_eq Set.Subset.rfl, hTwo]
    have hContractRank : (Matroid.contract M X).eRank = 2 :=
      eRank_contract_eq_two_of_eRank_eq_four_eRk_eq_two
        M hRank hX.1 hTwo
    have hRestrictCard :
        (Matroid.restrict M X).E.encard = ((2 * k : ℕ) : ℕ∞) := by
      simpa [Matroid.restrict_ground_eq] using hXcard
    have hContractCard :
        (Matroid.contract M X).E.encard = ((2 * k : ℕ) : ℕ∞) := by
      simpa [Matroid.contract_ground] using hComplementCard
    obtain ⟨σS, hS⟩ :=
      exists_cyclicBasisOrder_of_rank_two
        (Matroid.restrict M X) k hk hRestrictFinite
        hRestrictRank hRestrictCard hRestrictDense
    obtain ⟨σT, hT⟩ :=
      exists_cyclicBasisOrder_of_rank_two
        (Matroid.contract M X) k hk hContractFinite
        hContractRank hContractCard hContractDense
    simpa using
      (exists_cyclicBasisOrder_of_balanced_restrict_contract
        (M := M) (X := X) (s := 2) (t := 2) (k := k)
        (by omega) (by omega) hk hX.1 σS σT hS hT)
  · have hXcard : X.encard = ((3 * k : ℕ) : ℕ∞) :=
      tight_encard_eq_three_mul_k_of_eRk_eq_three M k hX hThree
    have hsum :
        X.encard + (M.E \ X).encard = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hX.1]
    have hComplementCard : (M.E \ X).encard = (k : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top
        (ENat.natCast_ne_top (3 * k))
      calc
        ((3 * k : ℕ) : ℕ∞) + (M.E \ X).encard =
            X.encard + (M.E \ X).encard := by rw [hXcard]
        _ = M.E.encard := hsum
        _ = ((4 * k : ℕ) : ℕ∞) := hEcard
        _ = ((3 * k : ℕ) : ℕ∞) + (k : ℕ∞) := by
          rw [← ENat.natCast_add]
          congr 1
          omega
    have hRestrictRank : (Matroid.restrict M X).eRank = 3 := by
      rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
        M.restrict_eRk_eq Set.Subset.rfl, hThree]
    have hContractRank : (Matroid.contract M X).eRank = 1 :=
      eRank_contract_eq_one_of_eRank_eq_four_eRk_eq_three
        M hRank hX.1 hThree
    have hRestrictCard :
        (Matroid.restrict M X).E.encard = ((3 * k : ℕ) : ℕ∞) := by
      simpa [Matroid.restrict_ground_eq] using hXcard
    have hContractCard :
        (Matroid.contract M X).E.encard = (k : ℕ∞) := by
      simpa [Matroid.contract_ground] using hComplementCard
    obtain ⟨σS, hS⟩ :=
      exists_cyclicBasisOrder_of_rank_three
        (Matroid.restrict M X) k hk hRestrictFinite
        hRestrictRank hRestrictCard hRestrictDense
    obtain ⟨σT, hT⟩ :=
      exists_cyclicBasisOrder_of_rank_one
        (Matroid.contract M X) k hk hContractFinite
        hContractRank hContractCard hContractDense
    simpa using
      (exists_cyclicBasisOrder_of_balanced_restrict_contract
        (M := M) (X := X) (s := 3) (t := 1) (k := k)
        (by omega) (by omega) hk hX.1 σS σT hS hT)

/-- Once the tight branch is discharged, rank-four KUM reduces exactly to strict density. -/
theorem exists_cyclicBasisOrder4_of_strict_case
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 4)
    (hEcard : M.E.encard = ((4 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    (hStrictCase :
      StrictlyUniformlyDense M k →
        ∃ order : Fin (4 * k) ≃ M.E,
          CyclicBasisOrder M 4 (by omega) order) :
    ∃ order : Fin (4 * k) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) order := by
  rcases exists_nonempty_proper_tight_or_strictlyUniformlyDense
      M k hDense with
    ⟨X, hX, hXnonempty, hXproper⟩ | hStrict
  · exact
      exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight
        M k hk hE hRank hEcard hDense
        hX hXnonempty hXproper
  · exact hStrictCase hStrict

#print axioms Rank3KUM.tight_rank_one_or_two_or_three_rank_four
#print axioms Rank3KUM.eRank_contract_add_eRk_eq_eRank
#print axioms Rank3KUM.exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight
#print axioms Rank3KUM.exists_cyclicBasisOrder4_of_strict_case

end

end Rank3KUM