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
    (hRank : M.eRank = 3)
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
    apply Set.nonempty_iff_ne_empty.2
    intro hAempty
    rw [hAempty, M.eRk_empty] at hArank
    simp at hArank
  have hAproper : A ≠ M.E := by
    intro hAEq
    have hground : M.eRk A = M.eRank := by
      rw [hAEq, M.eRk_ground]
    rw [hArank, hRank] at hground
    norm_num at hground
  have hlt :=
    StrictlyUniformlyDense.encard_lt_two_mul_k_of_eRk_eq_two
      M k hStrict hAE hAnonempty hAproper hArank
  have hltNat : A.ncard < 2 * k := by
    rw [← hAfin.cast_ncard_eq] at hlt
    exact_mod_cast hlt
  have hleNat : A.ncard ≤ (k - 1) * 2 := by
    by_contra hnot
    have hcard : A.ncard = 2 * k - 1 := by
      omega
    obtain ⟨e, heA, heD⟩ :=
      hHits A hAE hArank hcard
    exact (hAcomp heA).2 heD
  rw [← hAfin.cast_ncard_eq]
  exact_mod_cast hleNat

/-- Two near-tight sets on a `3k`-element ground set overlap in at least `k-2` elements. -/
theorem k_sub_two_le_ncard_inter_of_nearTight
    (M : Matroid α) (k : ℕ)
    (hE : M.E.Finite)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    {A B : Set α}
    (hAE : A ⊆ M.E)
    (hBE : B ⊆ M.E)
    (hAcard : A.ncard = 2 * k - 1)
    (hBcard : B.ncard = 2 * k - 1) :
    k - 2 ≤ (A ∩ B).ncard := by
  have hEncard : M.E.ncard = 3 * k := by
    have hcast :
        (M.E.ncard : ℕ∞) =
          ((3 * k : ℕ) : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  have hAfin : A.Finite :=
    hE.subset hAE
  have hBfin : B.Finite :=
    hE.subset hBE
  have hUnionLe :
      (A ∪ B).ncard ≤ M.E.ncard :=
    Set.ncard_le_ncard
      (Set.union_subset hAE hBE) hE
  have hCount :=
    Set.ncard_union_add_ncard_inter
      A B hAfin hBfin
  rw [hAcard, hBcard, hEncard] at hCount hUnionLe
  omega

/-- Every near-tight rank-two set in the strict case is already a flat. -/
theorem isFlat_of_strict_rankTwo_ncard_eq
    (M : Matroid α) (k : ℕ)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M k)
    {A : Set α}
    (hAE : A ⊆ M.E)
    (hArank : M.eRk A = 2)
    (hAcard : A.ncard = 2 * k - 1) :
    M.IsFlat A := by
  have hAfin : A.Finite :=
    hE.subset hAE
  have hAnonempty : A.Nonempty := by
    apply Set.nonempty_iff_ne_empty.2
    intro hAempty
    subst A
    simp at hArank
  have hAproper : A ≠ M.E := by
    intro hAEq
    have hground : M.eRk A = M.eRank := by
      rw [hAEq, M.eRk_ground]
    rw [hArank, hRank] at hground
    norm_num at hground
  have hClosureFinite :
      (M.closure A).Finite :=
    hE.subset (M.closure_subset_ground A)
  have hClosureRank :
      M.eRk (M.closure A) = 2 := by
    rw [M.eRk_closure_eq, hArank]
  have hClosureNonempty : (M.closure A).Nonempty :=
    hAnonempty.mono (M.subset_closure A hAE)
  have hClosureProper : M.closure A ≠ M.E := by
    intro hEq
    have hground : M.eRk (M.closure A) = M.eRank := by
      rw [hEq, M.eRk_ground]
    rw [hClosureRank, hRank] at hground
    norm_num at hground
  have hClosureLt :=
    StrictlyUniformlyDense.encard_lt_two_mul_k_of_eRk_eq_two
      M k hStrict (M.closure_subset_ground A)
      hClosureNonempty hClosureProper hClosureRank
  have hClosureNcardLt :
      (M.closure A).ncard < 2 * k := by
    rw [← hClosureFinite.cast_ncard_eq] at hClosureLt
    exact_mod_cast hClosureLt
  have hClosureNcardLe :
      (M.closure A).ncard ≤ A.ncard := by
    omega
  have hClosureEq :
      M.closure A = A :=
    hClosureFinite.eq_of_subset_of_ncard_le
      (M.subset_closure A hAE) hClosureNcardLe
  exact Matroid.isFlat_iff_closure_eq.2 hClosureEq

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
      have heA : e ∈ A := by
        rw [hAEq]
        exact hD.subset_ground heD
      exact (hAcomp heA).2 heD
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
      rw [← hAfin.cast_ncard_eq] at hlt
      exact_mod_cast hlt
    have hleNat : A.ncard ≤ k - 1 := by
      omega
    rw [← hAfin.cast_ncard_eq]
    have hleCast :
        (A.ncard : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hleNat
    simpa [hr] using hleCast
  · have hArankTwo : M.eRk A = 2 := by
      simpa using hr
    rw [hArankTwo]
    exact hRankTwo A hAcomp hArankTwo
  · have hcard :
        A.encard ≤ ((3 * (k - 1) : ℕ) : ℕ∞) := by
      calc
        A.encard ≤ (M.E \ D).encard :=
          Set.encard_mono hAcomp
        _ = ((3 * (k - 1) : ℕ) : ℕ∞) :=
          hComplementCard
    simpa [hr, Nat.mul_comm] using hcard

/--
A rank-preserving basis that hits every near-tight rank-two set is
density-reducing.
-/
theorem uniformlyDense_delete_of_strict_of_hitsNearTight
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
    (hHits : HitsNearTightRankTwo M k D) :
    UniformlyDense (Matroid.delete M D) (k - 1) := by
  apply uniformlyDense_delete_of_strict_of_rank_two_bound
    M k hk hE hRank hDense hStrict hD hComplementCard
  intro A hAcomp hArank
  exact
    rankTwoComplementBound_of_hitsNearTight
      M k hE hRank hStrict hHits hAcomp hArank

/-- In a strict rank-three instance with `k ≥ 3`, deleting any basis preserves rank. -/
theorem eRank_delete_eq_three_of_strict
    (M : Matroid α) (k : ℕ)
    (hk : 3 ≤ k)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M k)
    {D : Set α}
    (hD : M.IsBase D)
    (hComplementCard :
      (M.E \ D).encard =
        ((3 * (k - 1) : ℕ) : ℕ∞)) :
    (Matroid.delete M D).eRank = 3 := by
  have hFormula :
      (Matroid.delete M D).eRank =
        M.eRk (M.E \ D) := by
    rw [Matroid.eRank_def,
      Matroid.delete_ground,
      Matroid.delete_eq_restrict,
      M.restrict_eRk_eq Set.Subset.rfl]
  rw [hFormula]
  by_contra hne
  have hrleThree : M.eRk (M.E \ D) ≤ 3 := by
    calc
      M.eRk (M.E \ D) ≤ M.eRank :=
        M.eRk_le_eRank _
      _ = 3 := hRank
  obtain ⟨r, hr, hrle⟩ :=
    ENat.le_natCast_iff.mp hrleThree
  have hrleTwo : M.eRk (M.E \ D) ≤ 2 := by
    rw [hr]
    have hrne : r ≠ 3 := by
      intro hre
      subst r
      exact hne (by simpa using hr)
    exact_mod_cast (show r ≤ 2 by omega)
  have hDcard : D.encard = (3 : ℕ∞) :=
    hD.encard_eq_eRank.trans hRank
  have hDnonempty : D.Nonempty := by
    apply Set.encard_ne_zero.mp
    rw [hDcard]
    norm_num
  have hComplementNonempty : (M.E \ D).Nonempty := by
    apply Set.encard_ne_zero.mp
    rw [hComplementCard]
    norm_num
    omega
  have hComplementProper : M.E \ D ≠ M.E := by
    intro heq
    obtain ⟨e, heD⟩ := hDnonempty
    have heComp : e ∈ M.E \ D := by
      rw [heq]
      exact hD.subset_ground heD
    exact heComp.2 heD
  have hlt :=
    hStrict (M.E \ D) Set.sdiff_subset
      hComplementNonempty hComplementProper
  have hltTwo :
      (M.E \ D).encard <
        ((2 * k : ℕ) : ℕ∞) := by
    refine hlt.trans_le ?_
    calc
      (k : ℕ∞) * M.eRk (M.E \ D) ≤
          (k : ℕ∞) * 2 := by
        exact mul_le_mul_left' hrleTwo _
      _ = ((2 * k : ℕ) : ℕ∞) := by
        rw [Nat.mul_comm]
        exact (ENat.natCast_mul k 2).symm
  rw [hComplementCard] at hltTwo
  have hltNat : 3 * (k - 1) < 2 * k := by
    exact_mod_cast hltTwo
  omega

#print axioms Rank3KUM.exists_nonempty_proper_tight_or_strictlyUniformlyDense
#print axioms Rank3KUM.StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one
#print axioms Rank3KUM.StrictlyUniformlyDense.encard_lt_two_mul_k_of_eRk_eq_two

end Rank3KUM
