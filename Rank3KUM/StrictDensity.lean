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

/--
A basis hits every near-tight rank-two set.  In the strict case these are
exactly the possible `2k-1` obstructions to lowering the density parameter.
-/
def HitsNearTightRankTwo
    (M : Matroid α) (k : ℕ) (D : Set α) : Prop :=
  ∀ A : Set α, A ⊆ M.E →
    M.eRk A = 2 →
    A.ncard = 2 * k - 1 →
    (A ∩ D).Nonempty

/-- A hit rules out the sole rank-two obstruction inside the complement. -/
theorem rankTwoComplementBound_of_hitsNearTight
    (M : Matroid α) (k : ℕ)
    (hE : M.E.Finite)
    (hStrict : StrictlyUniformlyDense M k)
    {D A : Set α}
    (hHits : HitsNearTightRankTwo M k D)
    (hAcomp : A ⊆ M.E \ D)
    (hArank : M.eRk A = 2) :
    A.encard ≤ ((k - 1 : ℕ) : ℕ∞) * 2 := by
  have hAE : A ⊆ M.E :=
    hAcomp.trans Set.sdiff_subset
  have hAfin : A.Finite :=
    hE.subset hAE
  have hAnonempty : A.Nonempty := by
    intro hAempty
    rw [hAempty, M.eRk_empty] at hArank
    simp at hArank
  have hAproper : A ≠ M.E := by
    intro hAEq
    have hDempty : D = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro e heD
      have heComp : e ∈ M.E \ D := by
        rw [← hAEq]
        exact hAcomp (hAE heD)
      exact heComp.2 heD
    subst D
    have hhit :=
      hHits A hAE hArank
    simp at hhit
  have hlt :=
    StrictlyUniformlyDense.encard_lt_two_mul_k_of_eRk_eq_two
      M k hStrict hAE hAnonempty hAproper hArank
  have hltNat : A.ncard < 2 * k := by
    rw [hAfin.cast_ncard_eq] at hlt
    exact_mod_cast hlt
  have hleNat : A.ncard ≤ (k - 1) * 2 := by
    by_contra hnot
    have hcard : A.ncard = 2 * k - 1 := by
      omega
    obtain ⟨e, heA, heD⟩ :=
      hHits A hAE hArank hcard
    exact (hAcomp heA).2 heD
  rw [hAfin.cast_ncard_eq]
  exact_mod_cast hleNat

/-- Deletion density can be checked using the original rank on subsets of the complement. -/
theorem uniformlyDense_delete_iff
    (M : Matroid α) (j : ℕ) (D : Set α) :
    UniformlyDense (Matroid.delete M D) j ↔
      ∀ A : Set α, A ⊆ M.E \ D →
        A.encard ≤ (j : ℕ∞) * M.eRk A := by
  constructor
  · intro h A hA
    have hAdelete : A ⊆ (Matroid.delete M D).E := by
      simpa using hA
    have hbound := h A hAdelete
    simpa [Matroid.delete_eq_restrict,
      M.restrict_eRk_eq hA] using hbound
  · intro h A hA
    have hAcomp : A ⊆ M.E \ D := by
      simpa using hA
    have hbound := h A hAcomp
    simpa [Matroid.delete_eq_restrict,
      M.restrict_eRk_eq hAcomp] using hbound

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

/--
In the strict case, after deleting a basis the density check is automatic in
ranks zero, one, and three.  Only rank-two subsets of the complement remain.
-/
theorem uniformlyDense_delete_of_strict_of_rank_two_bound
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hDense : UniformlyDense M k)
    (hStrict : StrictlyUniformlyDense M k)
    {D : Set α}
    (hD : M.IsBase D)
    (hComplementCard :
      (M.E \ D).encard =
        ((3 * (k - 1) : ℕ) : ℕ∞))
    (hRankTwo :
      ∀ A : Set α, A ⊆ M.E \ D →
        M.eRk A = 2 →
        A.encard ≤
          ((k - 1 : ℕ) : ℕ∞) * 2) :
    UniformlyDense (Matroid.delete M D) (k - 1) := by
  rw [uniformlyDense_delete_iff]
  intro A hAcomp
  have hAE : A ⊆ M.E :=
    hAcomp.trans Set.sdiff_subset
  have hAfin : A.Finite :=
    hE.subset hAE
  by_cases hAempty : A = ∅
  · subst A
    simp
  have hAnonempty : A.Nonempty :=
    Set.nonempty_iff_ne_empty.2 hAempty
  have hAproper : A ≠ M.E := by
    intro hAEq
    have hDempty : D = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro e heD
      have heComp : e ∈ M.E \ D := by
        rw [← hAEq]
        exact hAcomp (hD.subset_ground heD)
      exact heComp.2 heD
    have hDcard : D.encard = (3 : ℕ∞) :=
      hD.encard_eq_eRank.trans hRank
    rw [hDempty] at hDcard
    simp at hDcard
  have hRkLe : M.eRk A ≤ 3 := by
    calc
      M.eRk A ≤ M.eRank := M.eRk_le_eRank A
      _ = 3 := hRank
  obtain ⟨r, hr, hrle⟩ :=
    ENat.le_natCast_iff.mp hRkLe
  have hRzero : r ≠ 0 := by
    intro hrzero
    subst r
    have hLoopless : M.Loopless :=
      loopless_of_uniformlyDense M k hk hDense
    letI : M.Loopless := hLoopless
    have hAloops : A ⊆ M.loops := by
      apply (M.eRk_eq_zero_iff hAE).mp
      simpa using hr
    rw [M.loops_eq_empty] at hAloops
    exact hAempty (Set.subset_empty_iff.mp hAloops)
  interval_cases r
  · exact (hRzero rfl).elim
  · have hlt :
        A.encard < (k : ℕ∞) :=
      StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one
        M k hStrict hAE hAnonempty hAproper (by simpa using hr)
    have hltNat : A.ncard < k := by
      rw [hAfin.cast_ncard_eq] at hlt
      exact_mod_cast hlt
    have hleNat : A.ncard ≤ k - 1 := by
      omega
    rw [hAfin.cast_ncard_eq]
    have hleCast :
        (A.ncard : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hleNat
    simpa [hr] using hleCast
  · exact
      hRankTwo A hAcomp (by simpa using hr)
  · have hcard :
        A.encard ≤ ((3 * (k - 1) : ℕ) : ℕ∞) := by
      calc
        A.encard ≤ (M.E \ D).encard :=
          Set.encard_mono hAcomp
        _ = ((3 * (k - 1) : ℕ) : ℕ∞) :=
          hComplementCard
    simpa [hr, Nat.mul_comm] using hcard

#print axioms Rank3KUM.exists_nonempty_proper_tight_or_strictlyUniformlyDense
#print axioms Rank3KUM.StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one
#print axioms Rank3KUM.StrictlyUniformlyDense.encard_lt_two_mul_k_of_eRk_eq_two

end Rank3KUM
