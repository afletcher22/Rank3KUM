import Rank3KUM.HalfWeave.RankTwo
import Rank3KUM.UniformDensity
import Mathlib.Order.Partition.Finpartition

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
