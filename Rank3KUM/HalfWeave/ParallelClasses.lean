import Rank3KUM.HalfWeave.RankTwo
import Rank3KUM.UniformDensity
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Fin

namespace Rank3KUM.HalfWeave

open Set

noncomputable section

variable {α : Type*}

/-- Ground elements are equivalent when their singleton closures agree. -/
def closureSetoid (M : Matroid α) : Setoid M.E where
  r e f :=
    M.closure ({(e : α)} : Set α) =
      M.closure ({(f : α)} : Set α)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/-- The finite partition of the ground set into singleton-closure classes. -/
def closureFinpartition
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    Finpartition (Finset.univ : Finset M.E) := by
  classical
  exact Finpartition.ofSetoid (closureSetoid M)

@[simp] theorem mem_closureFinpartition_part_iff
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (e f : M.E) :
    f ∈ (closureFinpartition M).part e ↔
      M.closure ({(e : α)} : Set α) =
        M.closure ({(f : α)} : Set α) := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel



/-- Closure parts sorted by nonincreasing cardinality. -/
def sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    List (closureFinpartition M).parts :=
  ((closureFinpartition M).parts.attach.toList).insertionSort
    (fun p q => q.1.card ≤ p.1.card)

@[simp] theorem length_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (sortedClosureParts M).length =
      (closureFinpartition M).parts.card := by
  simp [sortedClosureParts]

@[simp] theorem mem_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (p : (closureFinpartition M).parts) :
    p ∈ sortedClosureParts M := by
  simp [sortedClosureParts]

theorem nodup_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (sortedClosureParts M).Nodup := by
  apply
    (List.perm_insertionSort
      (fun p q :
        (closureFinpartition M).parts =>
          q.1.card ≤ p.1.card)
      ((closureFinpartition M).parts.attach.toList)).nodup_iff.mpr
  exact Finset.nodup_toList _

theorem pairwise_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (sortedClosureParts M).Pairwise
      (fun p q => q.1.card ≤ p.1.card) := by
  exact List.pairwise_insertionSort _ _

#print axioms Rank3KUM.HalfWeave.nodup_sortedClosureParts
#print axioms Rank3KUM.HalfWeave.pairwise_sortedClosureParts


/-- Enumerate closure parts in their nonincreasing-size order. -/
def sortedClosurePartsEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    Fin (closureFinpartition M).parts.card ≃
      (closureFinpartition M).parts := by
  let L := sortedClosureParts M
  have hlength :
      L.length = (closureFinpartition M).parts.card := by
    simpa [L] using length_sortedClosureParts M
  have hnodup : L.Nodup := by
    simpa [L] using nodup_sortedClosureParts M
  have hall :
      ∀ p : (closureFinpartition M).parts,
        p ∈ L := by
    intro p
    simpa [L] using mem_sortedClosureParts M p
  exact
    (finCongr hlength.symm).trans
      (hnodup.getEquivOfForallMemList _ hall)

#print axioms Rank3KUM.HalfWeave.sortedClosurePartsEquiv


/-- The sizes of the sorted closure parts sum to the ground-set cardinality. -/
theorem sum_sortedClosureParts_card
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (∑ i : Fin (closureFinpartition M).parts.card,
      ((sortedClosurePartsEquiv M i).1).card) =
        Fintype.card M.E := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  calc
    (∑ i : Fin (closureFinpartition M).parts.card,
      ((sortedClosurePartsEquiv M i).1).card) =
        ∑ p : (closureFinpartition M).parts,
          p.1.card := by
      refine Fintype.sum_equiv
        (sortedClosurePartsEquiv M) _ _ ?_
      intro i
      rfl
    _ = ∑ p ∈ (closureFinpartition M).parts,
        p.card := by
      change
        (∑ p ∈ (closureFinpartition M).parts.attach,
          p.1.card) =
            ∑ p ∈ (closureFinpartition M).parts, p.card
      exact
        Finset.sum_attach
          (closureFinpartition M).parts
          (fun p : Finset M.E => p.card)
    _ = (Finset.univ : Finset M.E).card := by
      simpa [P] using P.sum_card_parts
    _ = Fintype.card M.E := by simp

#print axioms Rank3KUM.HalfWeave.sum_sortedClosureParts_card


/--
Flatten the sorted family of closure parts into contiguous
`(part index, offset)` coordinates.
-/
def sortedClosureSigmaEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) ≃
      (i : Fin (closureFinpartition M).parts.card) ×
        Fin ((sortedClosurePartsEquiv M i).1).card := by
  have hsum :
      (∑ i : Fin (closureFinpartition M).parts.card,
        ((sortedClosurePartsEquiv M i).1).card) =
          2 * k := by
    rw [sum_sortedClosureParts_card M, hcard]
  exact
    (finCongr hsum.symm).trans
      finSigmaFinEquiv.symm

#print axioms Rank3KUM.HalfWeave.sortedClosureSigmaEquiv


/-- Identify the ground subtype with the subtype of the universal finset. -/
def groundUnivFinsetEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    M.E ≃ (Finset.univ : Finset M.E) where
  toFun e := ⟨e, Finset.mem_univ e⟩
  invFun e := e.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- Enumerate every closure part internally by its finite cardinality. -/
def closurePartsEnumeration
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    M.E ≃
      (p : (closureFinpartition M).parts) ×
        Fin p.1.card :=
  (groundUnivFinsetEquiv M).trans
    ((closureFinpartition M).equivSigmaParts.trans
      ((Equiv.refl _).sigmaCongr
        (fun p => p.1.equivFin)))

@[simp] theorem closurePartsEnumeration_part
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (e : M.E) :
    ((closurePartsEnumeration M e).1).1 =
      (closureFinpartition M).part e := by
  rfl

/-- Reindex the internally enumerated closure parts by decreasing size. -/
def sortedClosureCoordinatesEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    ((i : Fin (closureFinpartition M).parts.card) ×
      Fin ((sortedClosurePartsEquiv M i).1).card) ≃
        M.E :=
  (Equiv.sigmaCongrLeft
      (sortedClosurePartsEquiv M)).trans
    (closurePartsEnumeration M).symm

theorem part_sortedClosureCoordinatesEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (z :
      (i : Fin (closureFinpartition M).parts.card) ×
        Fin ((sortedClosurePartsEquiv M i).1).card) :
    (closureFinpartition M).part
        (sortedClosureCoordinatesEquiv M z) =
      (sortedClosurePartsEquiv M z.1).1 := by
  let q :
      (p : (closureFinpartition M).parts) ×
        Fin p.1.card :=
    ⟨sortedClosurePartsEquiv M z.1, z.2⟩
  change
    (closureFinpartition M).part
        ((closurePartsEnumeration M).symm q) =
      (sortedClosurePartsEquiv M z.1).1
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
    _ = (sortedClosurePartsEquiv M z.1).1 := by
      rfl

/-- A ground-set enumeration in which closure classes form sorted contiguous blocks. -/
def sortedClosureGroundEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) ≃ M.E :=
  (sortedClosureSigmaEquiv M k hcard).trans
    (sortedClosureCoordinatesEquiv M)

/-- The sorted closure-class label attached to a flattened ground position. -/
def sortedClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) →
      Fin (closureFinpartition M).parts.card :=
  fun j => (sortedClosureSigmaEquiv M k hcard j).1

theorem part_sortedClosureGroundEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (j : Fin (2 * k)) :
    (closureFinpartition M).part
        (sortedClosureGroundEquiv M k hcard j) =
      (sortedClosurePartsEquiv M
        (sortedClosureBlock M k hcard j)).1 := by
  simpa [sortedClosureGroundEquiv, sortedClosureBlock] using
    part_sortedClosureCoordinatesEquiv M
      (sortedClosureSigmaEquiv M k hcard j)

theorem mem_sortedClosurePart_iff_block_eq
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (j : Fin (2 * k))
    (c : Fin (closureFinpartition M).parts.card) :
    sortedClosureGroundEquiv M k hcard j ∈
        (sortedClosurePartsEquiv M c).1 ↔
      sortedClosureBlock M k hcard j = c := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  rw [← P.part_eq_iff_mem
    (sortedClosurePartsEquiv M c).2]
  rw [part_sortedClosureGroundEquiv]
  constructor
  · intro h
    apply (sortedClosurePartsEquiv M).injective
    exact Subtype.ext h
  · intro h
    subst c
    rfl

/-- Every block fiber is in bijection with its sorted closure part. -/
theorem card_fiberFinset_sortedClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (c : Fin (closureFinpartition M).parts.card) :
    (fiberFinset
      (sortedClosureBlock M k hcard) c).card =
        ((sortedClosurePartsEquiv M c).1).card := by
  exact
    Finset.card_bijective
      (sortedClosureGroundEquiv M k hcard)
      (sortedClosureGroundEquiv M k hcard).bijective
      (fun j => by
        simp only [fiberFinset, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact
          (mem_sortedClosurePart_iff_block_eq
            M k hcard j c).symm)

/-- Every sorted closure label occurs among the flattened ground positions. -/
theorem sortedClosureBlock_surjective
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Function.Surjective
      (sortedClosureBlock M k hcard) := by
  intro c
  have hpart :
      ((sortedClosurePartsEquiv M c).1).Nonempty :=
    (closureFinpartition M).nonempty_of_mem_parts
      (sortedClosurePartsEquiv M c).2
  have hpos :
      0 < ((sortedClosurePartsEquiv M c).1).card :=
    Finset.card_pos.mpr hpart
  have hfiber :
      0 <
        (fiberFinset
          (sortedClosureBlock M k hcard) c).card := by
    rw [card_fiberFinset_sortedClosureBlock]
    exact hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hfiber
  refine ⟨j, ?_⟩
  simpa [fiberFinset] using hj

#print axioms Rank3KUM.HalfWeave.groundUnivFinsetEquiv
#print axioms Rank3KUM.HalfWeave.closurePartsEnumeration
#print axioms Rank3KUM.HalfWeave.sortedClosureCoordinatesEquiv
#print axioms Rank3KUM.HalfWeave.sortedClosureGroundEquiv

/-- Every part of the closure partition inherits the uniform-density bound. -/
theorem card_closureFinpartition_part_le
    (M : Matroid α)
    (k : ℕ)
    (hDense : UniformlyDense M k)
    (hLoopless : M.Loopless)
    [Fintype M.E]
    [DecidableEq M.E]
    (p : Finset M.E)
    (hp : p ∈ (closureFinpartition M).parts) :
    p.card ≤ k := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  obtain ⟨e, he⟩ :=
    P.nonempty_of_mem_parts (by simpa [P] using hp)
  have hpart : P.part e = p :=
    P.part_eq_of_mem
      (by simpa [P] using hp) he
  have himage :
      (fun x : M.E => (x : α)) ''
          (↑p : Set M.E) ⊆
        M.closure ({(e : α)} : Set α) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxpart : x ∈ P.part e := by
      rw [hpart]
      exact hx
    have hclosure :
        M.closure ({(e : α)} : Set α) =
          M.closure ({(x : α)} : Set α) :=
      (mem_closureFinpartition_part_iff M e x).1
        (by simpa [P] using hxpart)
    rw [hclosure]
    exact M.mem_closure_self (x : α) x.property
  have hcardENat : (p.card : ℕ∞) ≤ (k : ℕ∞) := by
    calc
      (p.card : ℕ∞) =
          (↑p : Set M.E).encard := by simp
      _ =
          ((fun x : M.E => (x : α)) ''
            (↑p : Set M.E)).encard :=
        (Subtype.val_injective.encard_image
          (↑p : Set M.E)).symm
      _ ≤ (M.closure
          ({(e : α)} : Set α)).encard :=
        Set.encard_mono himage
      _ ≤ (k : ℕ∞) :=
        closure_singleton_encard_le
          M k hDense hLoopless e.property
  exact_mod_cast hcardENat

#print axioms Rank3KUM.HalfWeave.card_closureFinpartition_part_le

/-- Rank two forces the closure partition to have at least two parts. -/
theorem two_le_card_closureFinpartition_parts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    2 ≤ (closureFinpartition M).parts.card := by
  obtain ⟨e, f, he, hf, hclosure⟩ :=
    exists_pair_closure_ne_of_eRank_eq_two M hRank
  let e' : M.E := ⟨e, he⟩
  let f' : M.E := ⟨f, hf⟩
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  have hparts_ne : P.part e' ≠ P.part f' := by
    intro hparts
    have hfmem : f' ∈ P.part f' := by
      simp [P]
    have hfmem' : f' ∈ P.part e' := by
      rwa [hparts]
    apply hclosure
    exact
      (mem_closureFinpartition_part_iff M e' f').1
        (by simpa [P] using hfmem')
  have hsubset :
      ({P.part e', P.part f'} :
        Finset (Finset M.E)) ⊆ P.parts := by
    intro p hp
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [P]
  calc
    2 = ({P.part e', P.part f'} :
      Finset (Finset M.E)).card := by
        symm
        exact Finset.card_pair hparts_ne
    _ ≤ P.parts.card :=
      Finset.card_le_card hsubset

#print axioms Rank3KUM.HalfWeave.mem_closureFinpartition_part_iff
#print axioms Rank3KUM.HalfWeave.two_le_card_closureFinpartition_parts

end

end Rank3KUM.HalfWeave
