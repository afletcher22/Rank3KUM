import Rank3KUM.HalfWeave.LargestFirstDirect
import Rank3KUM.Version2.HalfWeave

namespace Rank3KUM.Version2.HalfWeave

open Rank3KUM.HalfWeave

noncomputable section

variable {α : Type*}

/--
Compatibility name for the direct largest-first constructor.  The substantive
construction now lives in the core HalfWeave layer.
-/
def rankTwoLargestFirstEnumerationOfUniformlyDense
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    RankTwoLargestFirstEnumeration M k
      (Rank3KUM.HalfWeave.closureFinpartition M).parts.card :=
  Rank3KUM.HalfWeave.rankTwoLargestFirstEnumerationOfUniformlyDense
    M k hk hcard hDense hRank

/--
Paper-v2 Proposition 4.2, constructed directly from the weakened
largest-first closure-class model.  The paper-level output no longer passes
through the internal `RankTwoSortedEnumeration` packaging.
-/
def cyclicRankTwoBasisOrderingOfUniformlyDenseDirect
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    CyclicRankTwoBasisOrdering M k hk := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let y :=
    Rank3KUM.HalfWeave.largestFirstClosureGroundEquiv
      M k hRank hcard
  let S :=
    Rank3KUM.HalfWeave.largestFirstClosureBlockModel
      M k hcard hDense hLoopless hRank
  refine
    { order := Rank3KUM.HalfWeave.woven k hk y
      adjacent_isBase := ?_ }
  intro p
  let a := Rank3KUM.HalfWeave.halfWeaveEquiv k hk p
  let b := Rank3KUM.HalfWeave.halfWeaveEquiv k hk
    (Rank3KUM.HalfWeave.weaveNext k hk p)
  have hblocks0 :=
    Rank3KUM.HalfWeave.largestFirst_woven_successor_blocks_ne
      hk S p
  have hblocks :
      Rank3KUM.HalfWeave.largestFirstClosureBlock
          M k hRank hcard a ≠
        Rank3KUM.HalfWeave.largestFirstClosureBlock
          M k hRank hcard b := by
    simpa [S, a, b,
      Rank3KUM.HalfWeave.largestFirstClosureBlockModel] using hblocks0
  have hclosure :
      M.closure ({((y a : M.E) : α)} : Set α) ≠
        M.closure ({((y b : M.E) : α)} : Set α) := by
    intro h
    apply hblocks
    exact
      (Rank3KUM.HalfWeave.largestFirstClosureBlock_eq_iff_closure_eq
        M k hRank hcard a b).2 (by simpa [y] using h)
  have hindep :
      M.Indep
        ({((y a : M.E) : α), ((y b : M.E) : α)} : Set α) :=
    Rank3KUM.HalfWeave.pair_indep_of_closure_ne
      M hLoopless (y a).property (y b).property hclosure
  have hne :
      ((y a : M.E) : α) ≠ ((y b : M.E) : α) := by
    intro hab
    apply hclosure
    rw [hab]
  have hbase :=
    Rank3KUM.HalfWeave.pair_isBase_of_indep_of_eRank_eq_two
      M hRank hne hindep
  simpa [Rank3KUM.HalfWeave.woven, a, b] using hbase

#print axioms Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDenseDirect

end

end Rank3KUM.Version2.HalfWeave