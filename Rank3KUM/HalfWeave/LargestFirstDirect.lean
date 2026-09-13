import Rank3KUM.HalfWeave.ParallelClasses
import Mathlib.Data.Finset.Max

namespace Rank3KUM.HalfWeave

open Set

noncomputable section

variable {α : Type*}

/-- Rank two makes the singleton-closure partition nonempty. -/
theorem closureFinpartition_parts_nonempty_of_eRank_eq_two
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    (closureFinpartition M).parts.Nonempty := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBcard : B.encard = 2 := by
    rw [hB.encard_eq_eRank, hRank]
  have hBne : B.Nonempty := by
    apply Set.nonempty_of_encard_ne_zero
    rw [hBcard]
    norm_num
  obtain ⟨e, heB⟩ := hBne
  let e' : M.E := ⟨e, hB.subset_ground heB⟩
  exact ⟨(closureFinpartition M).part e', by simp⟩

/-- A rank-two closure partition has a part of maximum cardinality. -/
theorem exists_largest_closure_part
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    ∃ p : (closureFinpartition M).parts,
      ∀ q : (closureFinpartition M).parts,
        q.1.card ≤ p.1.card := by
  obtain ⟨p0, hp0⟩ :=
    closureFinpartition_parts_nonempty_of_eRank_eq_two M hRank
  let p0' : (closureFinpartition M).parts := ⟨p0, hp0⟩
  have hnonempty :
      (Finset.univ : Finset ((closureFinpartition M).parts)).Nonempty :=
    ⟨p0', Finset.mem_univ _⟩
  obtain ⟨p, _hp, hmax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset ((closureFinpartition M).parts))
      (fun q => q.1.card) hnonempty
  exact ⟨p, fun q => hmax q (Finset.mem_univ q)⟩

/-- A chosen largest singleton-closure class. -/
def largestClosurePart
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    (closureFinpartition M).parts :=
  Classical.choose (exists_largest_closure_part M hRank)

/-- Every closure class is no larger than the chosen largest class. -/
theorem card_le_largestClosurePart
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (q : (closureFinpartition M).parts) :
    q.1.card ≤ (largestClosurePart M hRank).1.card :=
  (Classical.choose_spec (exists_largest_closure_part M hRank)) q

/-- Enumerate closure classes arbitrarily, except that a largest class is first. -/
def largestFirstClosurePartsEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    Fin (closureFinpartition M).parts.card ≃
      (closureFinpartition M).parts := by
  let E : Fin (closureFinpartition M).parts.card ≃
      (closureFinpartition M).parts :=
    ((closureFinpartition M).parts.equivFin).symm
  let p := largestClosurePart M hRank
  let i := E.symm p
  have hpos : 0 < (closureFinpartition M).parts.card :=
    Finset.card_pos.mpr
      (closureFinpartition_parts_nonempty_of_eRank_eq_two M hRank)
  let z : Fin (closureFinpartition M).parts.card := ⟨0, hpos⟩
  exact (Equiv.swap z i).trans E

/-- The zero class label is the chosen largest closure class. -/
theorem largestFirstClosurePartsEquiv_zero
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hpos : 0 < (closureFinpartition M).parts.card) :
    largestFirstClosurePartsEquiv M hRank ⟨0, hpos⟩ =
      largestClosurePart M hRank := by
  classical
  let E : Fin (closureFinpartition M).parts.card ≃
      (closureFinpartition M).parts :=
    ((closureFinpartition M).parts.equivFin).symm
  let p := largestClosurePart M hRank
  let i := E.symm p
  let z : Fin (closureFinpartition M).parts.card := ⟨0, hpos⟩
  change ((Equiv.swap z i).trans E) z = p
  simp [i, z]

/-- The closure-part cardinalities sum to the ground-set cardinality. -/
theorem sum_closureFinpartition_parts_card
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (∑ p : (closureFinpartition M).parts, p.1.card) =
      Fintype.card M.E := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  calc
    (∑ p : (closureFinpartition M).parts, p.1.card) =
        ∑ p ∈ (closureFinpartition M).parts, p.card := by
      change
        (∑ p ∈ (closureFinpartition M).parts.attach, p.1.card) =
          ∑ p ∈ (closureFinpartition M).parts, p.card
      exact
        Finset.sum_attach
          (closureFinpartition M).parts
          (fun p : Finset M.E => p.card)
    _ = (Finset.univ : Finset M.E).card := by
      simpa [P] using P.sum_card_parts
    _ = Fintype.card M.E := by simp

/-- Reindexing the closure classes preserves the total block size. -/
theorem sum_largestFirstClosureParts_card
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    (∑ i : Fin (closureFinpartition M).parts.card,
      ((largestFirstClosurePartsEquiv M hRank i).1).card) =
        Fintype.card M.E := by
  calc
    (∑ i : Fin (closureFinpartition M).parts.card,
      ((largestFirstClosurePartsEquiv M hRank i).1).card) =
        ∑ p : (closureFinpartition M).parts, p.1.card := by
      refine Fintype.sum_equiv
        (largestFirstClosurePartsEquiv M hRank) _ _ ?_
      intro i
      rfl
    _ = Fintype.card M.E :=
      sum_closureFinpartition_parts_card M

/-- Flatten the largest-first family of closure classes into contiguous blocks. -/
def largestFirstClosureSigmaEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) ≃
      (i : Fin (closureFinpartition M).parts.card) ×
        Fin ((largestFirstClosurePartsEquiv M hRank i).1).card := by
  have hsum :
      (∑ i : Fin (closureFinpartition M).parts.card,
        ((largestFirstClosurePartsEquiv M hRank i).1).card) =
          2 * k := by
    rw [sum_largestFirstClosureParts_card M hRank, hcard]
  exact
    (finCongr hsum.symm).trans
      finSigmaFinEquiv.symm

/-- Convert largest-first block coordinates back into ground elements. -/
def largestFirstClosureCoordinatesEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    ((i : Fin (closureFinpartition M).parts.card) ×
      Fin ((largestFirstClosurePartsEquiv M hRank i).1).card) ≃
        M.E :=
  (Equiv.sigmaCongrLeft
      (largestFirstClosurePartsEquiv M hRank)).trans
    (closurePartsEnumeration M).symm

/-- The closure part of a largest-first coordinate is its block label. -/
theorem part_largestFirstClosureCoordinatesEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (z :
      (i : Fin (closureFinpartition M).parts.card) ×
        Fin ((largestFirstClosurePartsEquiv M hRank i).1).card) :
    (closureFinpartition M).part
        (largestFirstClosureCoordinatesEquiv M hRank z) =
      (largestFirstClosurePartsEquiv M hRank z.1).1 := by
  let q :
      (p : (closureFinpartition M).parts) × Fin p.1.card :=
    ⟨largestFirstClosurePartsEquiv M hRank z.1, z.2⟩
  change
    (closureFinpartition M).part
        ((closurePartsEnumeration M).symm q) =
      (largestFirstClosurePartsEquiv M hRank z.1).1
  calc
    (closureFinpartition M).part
        ((closurePartsEnumeration M).symm q) =
      ((closurePartsEnumeration M
        ((closurePartsEnumeration M).symm q)).1).1 := by
          symm
          exact
            closurePartsEnumeration_part M
              ((closurePartsEnumeration M).symm q)
    _ = q.1.1 := by
      exact congrArg (fun x => x.1.1)
        ((closurePartsEnumeration M).apply_symm_apply q)
    _ = (largestFirstClosurePartsEquiv M hRank z.1).1 := by
      rfl

/-- The direct largest-first ground-set enumeration. -/
def largestFirstClosureGroundEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) ≃ M.E :=
  (largestFirstClosureSigmaEquiv M k hRank hcard).trans
    (largestFirstClosureCoordinatesEquiv M hRank)

/-- The direct largest-first block label of a flattened ground position. -/
def largestFirstClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) → Fin (closureFinpartition M).parts.card :=
  fun j => (largestFirstClosureSigmaEquiv M k hRank hcard j).1

/-- The closure part of a flattened ground position is its largest-first block. -/
theorem part_largestFirstClosureGroundEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k)
    (j : Fin (2 * k)) :
    (closureFinpartition M).part
        (largestFirstClosureGroundEquiv M k hRank hcard j) =
      (largestFirstClosurePartsEquiv M hRank
        (largestFirstClosureBlock M k hRank hcard j)).1 := by
  simpa [largestFirstClosureGroundEquiv, largestFirstClosureBlock] using
    part_largestFirstClosureCoordinatesEquiv M hRank
      (largestFirstClosureSigmaEquiv M k hRank hcard j)

/-- The direct largest-first block labels are monotone because blocks are contiguous. -/
theorem monotone_largestFirstClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k) :
    Monotone (largestFirstClosureBlock M k hRank hcard) := by
  have hsum :
      (∑ i : Fin (closureFinpartition M).parts.card,
        ((largestFirstClosurePartsEquiv M hRank i).1).card) =
          2 * k := by
    rw [sum_largestFirstClosureParts_card M hRank, hcard]
  intro a b hab
  change
    (finSigmaFinEquiv.symm
      (finCongr hsum.symm a)).1 ≤
    (finSigmaFinEquiv.symm
      (finCongr hsum.symm b)).1
  apply monotone_finSigmaFinEquiv_symm_fst
  change a.val ≤ b.val
  exact hab

/-- Ground membership in a closure part is equivalent to equality of block labels. -/
theorem mem_largestFirstClosurePart_iff_block_eq
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k)
    (j : Fin (2 * k))
    (c : Fin (closureFinpartition M).parts.card) :
    largestFirstClosureGroundEquiv M k hRank hcard j ∈
        (largestFirstClosurePartsEquiv M hRank c).1 ↔
      largestFirstClosureBlock M k hRank hcard j = c := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  rw [← P.part_eq_iff_mem
    (largestFirstClosurePartsEquiv M hRank c).2]
  change
    (closureFinpartition M).part
        (largestFirstClosureGroundEquiv M k hRank hcard j) =
      (largestFirstClosurePartsEquiv M hRank c).1 ↔
    largestFirstClosureBlock M k hRank hcard j = c
  rw [part_largestFirstClosureGroundEquiv]
  constructor
  · intro h
    apply (largestFirstClosurePartsEquiv M hRank).injective
    exact Subtype.ext h
  · intro h
    subst c
    rfl

/-- Every block fiber has the cardinality of its closure part. -/
theorem card_fiberFinset_largestFirstClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k)
    (c : Fin (closureFinpartition M).parts.card) :
    (fiberFinset
      (largestFirstClosureBlock M k hRank hcard) c).card =
        ((largestFirstClosurePartsEquiv M hRank c).1).card := by
  exact
    Finset.card_bijective
      (largestFirstClosureGroundEquiv M k hRank hcard)
      (largestFirstClosureGroundEquiv M k hRank hcard).bijective
      (fun j => by
        simp only [fiberFinset, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact
          (mem_largestFirstClosurePart_iff_block_eq
            M k hRank hcard j c).symm)

/-- Every largest-first block label occurs.  Retained as a reusable fact. -/
theorem largestFirstClosureBlock_surjective
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k) :
    Function.Surjective
      (largestFirstClosureBlock M k hRank hcard) := by
  intro c
  have hpart :
      ((largestFirstClosurePartsEquiv M hRank c).1).Nonempty :=
    (closureFinpartition M).nonempty_of_mem_parts
      (largestFirstClosurePartsEquiv M hRank c).2
  have hpos : 0 < ((largestFirstClosurePartsEquiv M hRank c).1).card :=
    Finset.card_pos.mpr hpart
  have hfiber :
      0 <
        (fiberFinset
          (largestFirstClosureBlock M k hRank hcard) c).card := by
    rw [card_fiberFinset_largestFirstClosureBlock]
    exact hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hfiber
  refine ⟨j, ?_⟩
  simpa [fiberFinset] using hj

/-- The first ground position belongs to block label zero. -/
theorem largestFirstClosureBlock_first_eq_zero
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k)
    (hk : 0 < k) :
    largestFirstClosureBlock M k hRank hcard
        (firstIndex k (zeroFin k hk)) =
      (⟨0, by
        exact Finset.card_pos.mpr
          (closureFinpartition_parts_nonempty_of_eRank_eq_two M hRank)⟩ :
        Fin (closureFinpartition M).parts.card) := by
  have hparts : (closureFinpartition M).parts.Nonempty :=
    closureFinpartition_parts_nonempty_of_eRank_eq_two M hRank
  have hpos : 0 < (closureFinpartition M).parts.card :=
    Finset.card_pos.mpr hparts
  let z : Fin (2 * k) := firstIndex k (zeroFin k hk)
  let c0 : Fin (closureFinpartition M).parts.card := ⟨0, hpos⟩
  have hc0part :
      ((largestFirstClosurePartsEquiv M hRank c0).1).Nonempty :=
    (closureFinpartition M).nonempty_of_mem_parts
      (largestFirstClosurePartsEquiv M hRank c0).2
  have hc0pos :
      0 < ((largestFirstClosurePartsEquiv M hRank c0).1).card :=
    Finset.card_pos.mpr hc0part
  let q :
      (i : Fin (closureFinpartition M).parts.card) ×
        Fin ((largestFirstClosurePartsEquiv M hRank i).1).card :=
    ⟨c0, ⟨0, hc0pos⟩⟩
  let j : Fin (2 * k) :=
    (largestFirstClosureSigmaEquiv M k hRank hcard).symm q
  have hj : largestFirstClosureBlock M k hRank hcard j = c0 := by
    change (largestFirstClosureSigmaEquiv M k hRank hcard j).1 = c0
    simp [j, q]
  have hzj : z ≤ j := by
    change z.val ≤ j.val
    have hzval : z.val = 0 := by
      simp [z, firstIndex, zeroFin]
    omega
  have hle :=
    monotone_largestFirstClosureBlock M k hRank hcard hzj
  rw [hj] at hle
  apply Fin.ext
  change (largestFirstClosureBlock M k hRank hcard z).val = 0
  have hle0 :
      (largestFirstClosureBlock M k hRank hcard z).val ≤ 0 := by
    simpa [c0] using hle
  omega

/-- Distinct direct block labels are exactly distinct singleton-closure classes. -/
theorem largestFirstClosureBlock_eq_iff_closure_eq
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2)
    (hcard : Fintype.card M.E = 2 * k)
    (a b : Fin (2 * k)) :
    largestFirstClosureBlock M k hRank hcard a =
        largestFirstClosureBlock M k hRank hcard b ↔
      M.closure
          ({((largestFirstClosureGroundEquiv M k hRank hcard a :
            M.E) : α)} : Set α) =
        M.closure
          ({((largestFirstClosureGroundEquiv M k hRank hcard b :
            M.E) : α)} : Set α) := by
  let y := largestFirstClosureGroundEquiv M k hRank hcard
  calc
    largestFirstClosureBlock M k hRank hcard a =
        largestFirstClosureBlock M k hRank hcard b ↔
      largestFirstClosureBlock M k hRank hcard b =
        largestFirstClosureBlock M k hRank hcard a := eq_comm
    _ ↔ y b ∈
        (largestFirstClosurePartsEquiv M hRank
          (largestFirstClosureBlock M k hRank hcard a)).1 :=
      (mem_largestFirstClosurePart_iff_block_eq
        M k hRank hcard b
          (largestFirstClosureBlock M k hRank hcard a)).symm
    _ ↔ M.closure
          ({((y a : M.E) : α)} : Set α) =
        M.closure
          ({((y b : M.E) : α)} : Set α) := by
      rw [← part_largestFirstClosureGroundEquiv
        M k hRank hcard a]
      exact
        mem_closureFinpartition_part_iff
          M (y a) (y b)

/-- The direct closure-class blocks satisfy exactly the largest-first hypotheses. -/
def largestFirstClosureBlockModel
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hLoopless : M.Loopless)
    (hRank : M.eRank = 2) :
    LargestFirstBlockModel k (closureFinpartition M).parts.card where
  block := largestFirstClosureBlock M k hRank hcard
  monotone_block :=
    monotone_largestFirstClosureBlock M k hRank hcard
  fiber_card_le := by
    intro c
    rw [card_fiberFinset_largestFirstClosureBlock]
    exact
      card_closureFinpartition_part_le
        M k hDense hLoopless
        (largestFirstClosurePartsEquiv M hRank c).1
        (largestFirstClosurePartsEquiv M hRank c).2
  first_fiber_largest := by
    intro hk c
    rw [largestFirstClosureBlock_first_eq_zero M k hRank hcard hk]
    rw [card_fiberFinset_largestFirstClosureBlock,
      card_fiberFinset_largestFirstClosureBlock]
    have hpos : 0 < (closureFinpartition M).parts.card :=
      Finset.card_pos.mpr
        (closureFinpartition_parts_nonempty_of_eRank_eq_two M hRank)
    have hmax :=
      card_le_largestClosurePart M hRank
        (largestFirstClosurePartsEquiv M hRank c)
    rw [largestFirstClosurePartsEquiv_zero M hRank hpos]
    exact hmax

/-- Uniform density directly supplies the weakened rank-two enumeration data. -/
def rankTwoLargestFirstEnumerationOfUniformlyDense
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    RankTwoSortedEnumeration M k
      (closureFinpartition M).parts.card := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let y := largestFirstClosureGroundEquiv M k hRank hcard
  let S :=
    largestFirstClosureBlockModel
      M k hcard hDense hLoopless hRank
  refine
    { y := y
      sortedBlocks := S
      indep_of_blocks_ne := ?_ }
  intro a b hab
  apply pair_indep_of_closure_ne
    M hLoopless (y a).property (y b).property
  intro hclosure
  apply hab
  exact
    (largestFirstClosureBlock_eq_iff_closure_eq
      M k hRank hcard a b).2 hclosure

#print axioms Rank3KUM.HalfWeave.rankTwoLargestFirstEnumerationOfUniformlyDense

end

end Rank3KUM.HalfWeave
