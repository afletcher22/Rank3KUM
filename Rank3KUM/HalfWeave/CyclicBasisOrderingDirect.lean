import Rank3KUM.HalfWeave.LargestFirstDirect

namespace Rank3KUM.HalfWeave

open Set

noncomputable section

variable {α : Type*}

/--
Uniform density in rank two directly yields the only output needed by the
tight-set branches: a cyclic enumeration whose woven successor pairs are
bases.  This avoids packaging the result through an intermediate enumeration
structure or a second paper-facing structure.
-/
theorem exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    ∃ order : Fin k × Bool ≃ M.E,
      ∀ p : Fin k × Bool,
        M.IsBase
          ({((order p : M.E) : α),
            ((order (weaveNext k hk p) : M.E) : α)} : Set α) := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let y := largestFirstClosureGroundEquiv M k hRank hcard
  let S :=
    largestFirstClosureBlockModel
      M k hcard hDense hLoopless hRank
  let order : Fin k × Bool ≃ M.E := woven k hk y
  refine ⟨order, ?_⟩
  intro p
  let a : Fin (2 * k) := halfWeaveEquiv k hk p
  let b : Fin (2 * k) :=
    halfWeaveEquiv k hk (weaveNext k hk p)
  have hblocks :
      largestFirstClosureBlock M k hRank hcard a ≠
        largestFirstClosureBlock M k hRank hcard b := by
    simpa [S, a, b] using
      (largestFirst_woven_successor_blocks_ne hk S p)
  have hclosure :
      M.closure ({((y a : M.E) : α)} : Set α) ≠
        M.closure ({((y b : M.E) : α)} : Set α) := by
    intro hcl
    apply hblocks
    exact
      (largestFirstClosureBlock_eq_iff_closure_eq
        M k hRank hcard a b).2 hcl
  have hab : a ≠ b := by
    intro hab
    apply hblocks
    exact congrArg
      (largestFirstClosureBlock M k hRank hcard) hab
  have hyne : y a ≠ y b := by
    intro hy
    exact hab (y.injective hy)
  have hne :
      ((y a : M.E) : α) ≠ ((y b : M.E) : α) := by
    intro hcoe
    apply hyne
    exact Subtype.ext hcoe
  have hindep :
      M.Indep
        ({((y a : M.E) : α),
          ((y b : M.E) : α)} : Set α) :=
    pair_indep_of_closure_ne
      M hLoopless (y a).property (y b).property hclosure
  have hbase :
      M.IsBase
        ({((y a : M.E) : α),
          ((y b : M.E) : α)} : Set α) :=
    pair_isBase_of_indep_of_eRank_eq_two M hRank hne hindep
  simpa [order, woven, a, b] using hbase

#print axioms Rank3KUM.HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense_direct

end

end Rank3KUM.HalfWeave
