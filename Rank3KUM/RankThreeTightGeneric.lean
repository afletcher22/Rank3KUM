import Rank3KUM.LowRankCyclicOneTwo
import Rank3KUM.UniformDensity

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- At rank three, the generic three-window predicate implies the legacy predicate. -/
theorem cyclicBasisOrder3_of_cyclicBasisOrder_three
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E)
    (h3 : CyclicBasisOrder M 3 hn σ) :
    CyclicBasisOrder3 M hn σ := by
  intro i
  have hset :
      cyclicWindow 3 hn σ i =
        ({(σ i : α),
          (σ (cyclicIndex n hn i 1) : α),
          (σ (cyclicIndex n hn i 2) : α)} : Set α) := by
    ext x
    simp only [cyclicWindow, Set.mem_range,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [cyclicIndex_zero]
    · rintro (hx | hx | hx)
      · subst x
        exact ⟨0, by simp [cyclicIndex_zero]⟩
      · subst x
        exact ⟨1, rfl⟩
      · subst x
        exact ⟨2, rfl⟩
  rw [← hset]
  exact h3 i

/-- Contracting rank `s` from finite ambient rank `s+t` leaves rank `t`. -/
theorem contract_eRank_eq_of_rank_sum_generic
    (M : Matroid α) {X : Set α} {s t : ℕ}
    (hX : X ⊆ M.E)
    (hRank : M.eRank = ((s + t : ℕ) : ℕ∞))
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
The entire nonempty proper tight-set branch in rank three, rebuilt through the
rank-independent balanced restriction/contraction gluing theorem.
-/
theorem exists_cyclicBasisOrder3_of_nonempty_proper_tight_generic
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hX : Tight M k X)
    (hXnonempty : X.Nonempty)
    (hXproper : X ≠ M.E) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXfinite : X.Finite := hE.subset hX.1
  have hComplementFinite : (M.E \ X).Finite :=
    hE.subset Set.sdiff_subset
  have hRestrictFinite : (Matroid.restrict M X).E.Finite := by
    simpa [Matroid.restrict_ground_eq] using hXfinite
  have hContractFinite : (Matroid.contract M X).E.Finite := by
    simpa [Matroid.contract_ground] using hComplementFinite
  obtain ⟨hRestrictDense, hContractDense⟩ :=
    UniformlyDense.tight_factors M k hDense hX hXfinite
  rcases
      tight_rank_one_or_two M k hE hRank hEcard hk hDense
        hX hXnonempty hXproper with hOne | hTwo
  · have hXcard : X.encard = (k : ℕ∞) :=
      tight_encard_eq_k_of_eRk_eq_one M k hX hOne
    have hsum :
        X.encard + (M.E \ X).encard = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hX.1]
    have hComplementCard :
        (M.E \ X).encard = ((2 * k : ℕ) : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top
        (by simp : (k : ℕ∞) ≠ ⊤)
      calc
        (k : ℕ∞) + (M.E \ X).encard =
            X.encard + (M.E \ X).encard := by rw [hXcard]
        _ = M.E.encard := hsum
        _ = ((3 * k : ℕ) : ℕ∞) := hEcard
        _ = (k : ℕ∞) + ((2 * k : ℕ) : ℕ∞) := by
          rw [← ENat.natCast_add]
          congr 1
          omega
    have hRestrictRank : (Matroid.restrict M X).eRank = 1 := by
      rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
        M.restrict_eRk_eq Set.Subset.rfl, hOne]
    have hRank12 : M.eRank = ((1 + 2 : ℕ) : ℕ∞) := by
      convert hRank using 1 <;> norm_num
    have hContractRank : (Matroid.contract M X).eRank = 2 :=
      contract_eRank_eq_of_rank_sum_generic
        (M := M) (X := X) (s := 1) (t := 2)
        hX.1 hRank12 hOne
    have hRestrictCard :
        (Matroid.restrict M X).E.encard = (k : ℕ∞) := by
      simpa [Matroid.restrict_ground_eq] using hXcard
    have hContractCard :
        (Matroid.contract M X).E.encard = ((2 * k : ℕ) : ℕ∞) := by
      simpa [Matroid.contract_ground] using hComplementCard
    obtain ⟨σS, hS⟩ :=
      exists_cyclicBasisOrder_of_rank_one
        (Matroid.restrict M X) k hk hRestrictFinite
        hRestrictRank hRestrictCard hRestrictDense
    obtain ⟨σT, hT⟩ :=
      exists_cyclicBasisOrder_of_rank_two
        (Matroid.contract M X) k hk hContractFinite
        hContractRank hContractCard hContractDense
    obtain ⟨order, horder⟩ :=
      exists_cyclicBasisOrder_of_balanced_restrict_contract
        (M := M) (X := X) (s := 1) (t := 2) (k := k)
        (by omega) (by omega) hk hX.1 σS σT hS hT
    refine ⟨?_, ?_⟩
    · simpa using order
    · simpa using
        (cyclicBasisOrder3_of_cyclicBasisOrder_three
          M (by omega) order horder)
  · have hXcard : X.encard = ((2 * k : ℕ) : ℕ∞) :=
      tight_encard_eq_two_mul_k_of_eRk_eq_two M k hX hTwo
    have hsum :
        X.encard + (M.E \ X).encard = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hX.1]
    have hComplementCard : (M.E \ X).encard = (k : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top
        (ENat.natCast_ne_top (2 * k))
      calc
        ((2 * k : ℕ) : ℕ∞) + (M.E \ X).encard =
            X.encard + (M.E \ X).encard := by rw [hXcard]
        _ = M.E.encard := hsum
        _ = ((3 * k : ℕ) : ℕ∞) := hEcard
        _ = ((2 * k : ℕ) : ℕ∞) + (k : ℕ∞) := by
          rw [← ENat.natCast_add]
          congr 1
          omega
    have hRestrictRank : (Matroid.restrict M X).eRank = 2 := by
      rw [Matroid.eRank_def, Matroid.restrict_ground_eq,
        M.restrict_eRk_eq Set.Subset.rfl, hTwo]
    have hRank21 : M.eRank = ((2 + 1 : ℕ) : ℕ∞) := by
      convert hRank using 1 <;> norm_num
    have hContractRank : (Matroid.contract M X).eRank = 1 :=
      contract_eRank_eq_of_rank_sum_generic
        (M := M) (X := X) (s := 2) (t := 1)
        hX.1 hRank21 hTwo
    have hRestrictCard :
        (Matroid.restrict M X).E.encard = ((2 * k : ℕ) : ℕ∞) := by
      simpa [Matroid.restrict_ground_eq] using hXcard
    have hContractCard :
        (Matroid.contract M X).E.encard = (k : ℕ∞) := by
      simpa [Matroid.contract_ground] using hComplementCard
    obtain ⟨σS, hS⟩ :=
      exists_cyclicBasisOrder_of_rank_two
        (Matroid.restrict M X) k hk hRestrictFinite
        hRestrictRank hRestrictCard hRestrictDense
    obtain ⟨σT, hT⟩ :=
      exists_cyclicBasisOrder_of_rank_one
        (Matroid.contract M X) k hk hContractFinite
        hContractRank hContractCard hContractDense
    obtain ⟨order, horder⟩ :=
      exists_cyclicBasisOrder_of_balanced_restrict_contract
        (M := M) (X := X) (s := 2) (t := 1) (k := k)
        (by omega) (by omega) hk hX.1 σS σT hS hT
    refine ⟨?_, ?_⟩
    · simpa using order
    · simpa using
        (cyclicBasisOrder3_of_cyclicBasisOrder_three
          M (by omega) order horder)

#print axioms Rank3KUM.cyclicBasisOrder3_of_cyclicBasisOrder_three
#print axioms Rank3KUM.contract_eRank_eq_of_rank_sum_generic
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_nonempty_proper_tight_generic

end

end Rank3KUM
