import Rank3KUM.HalfWeave.ParallelClasses
import Rank3KUM.Interleave

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
A uniformly dense rank-two flat of size `2k`, with a complement of size `k`,
canonically supplies the sorted half-weave enumeration and hence a cyclic
rank-three basis order.
-/
theorem exists_cyclicBasisOrder3_of_uniformlyDense_rankTwo_flat
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hDense : UniformlyDense M k)
    {X : Set α}
    (hRestrictRank : (M.restrict X).eRank = 2)
    (hXflat : M.IsFlat X)
    (hXcard : X.encard = ((2 * k : ℕ) : ℕ∞))
    (hComplementCard : (M.E \ X).encard = (k : ℕ∞)) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hXfinite : X.Finite :=
    hE.subset hXflat.subset_ground
  letI : Fintype X := hXfinite.fintype
  letI : Fintype (M.restrict X).E :=
    Fintype.ofEquiv X (restrictGroundEquiv M X).symm
  letI : DecidableEq (M.restrict X).E :=
    Classical.decEq _
  have hXncard : X.ncard = 2 * k := by
    have hcast : (X.ncard : ℕ∞) =
        ((2 * k : ℕ) : ℕ∞) := by
      rw [hXfinite.cast_ncard_eq]
      exact hXcard
    exact_mod_cast hcast
  have hRestrictCard :
      Fintype.card (M.restrict X).E = 2 * k := by
    calc
      Fintype.card (M.restrict X).E =
          Fintype.card X :=
        Fintype.card_congr (restrictGroundEquiv M X)
      _ = Nat.card X := Fintype.card_eq_nat_card
      _ = X.ncard := by
        simp only [Nat.card_coe_set_eq]
      _ = 2 * k := hXncard
  have hRestrictDense : UniformlyDense (M.restrict X) k :=
    UniformlyDense.restrict M k hDense hXflat.subset_ground
  have hRestrictLoopless : (M.restrict X).Loopless :=
    loopless_of_uniformlyDense
      (M.restrict X) k hk hRestrictDense
  let D :=
    HalfWeave.rankTwoSortedEnumerationOfUniformlyDense
      (M.restrict X) k hRestrictCard hRestrictDense
      hRestrictLoopless hRestrictRank
  exact
    exists_cyclicBasisOrder3_of_sortedEnumeration_tight_flat
      M hk hE hRank hRestrictRank hXflat
      hComplementCard D

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_uniformlyDense_rankTwo_flat

end

end Rank3KUM
