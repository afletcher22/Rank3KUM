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
Paper-v2 compatibility endpoint for Proposition 4.2 using the direct
largest-first construction now housed in the core layer.
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
  let D :=
    rankTwoLargestFirstEnumerationOfUniformlyDense
      M k hk hcard hDense hRank
  exact cyclicRankTwoBasisOrderingOfLargestFirst M hk hRank D

#print axioms Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDenseDirect

end

end Rank3KUM.Version2.HalfWeave
