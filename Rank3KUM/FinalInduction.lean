import Rank3KUM.FinalReduction
import Rank3KUM.SmallCases

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
Strong induction completes the theorem once two sharply isolated inputs are
available: the six-element case and a density-reducing basis in every strict
case with `k ≥ 3`.
-/
theorem rankThreeKUM_of_small_two_and_strict_deletion
    (hTwo :
      ∀ N : Matroid α,
        N.E.Finite →
        N.eRank = 3 →
        N.E.encard = (6 : ℕ∞) →
        UniformlyDense N 2 →
        ∃ order : Fin 6 ≃ N.E,
          CyclicBasisOrder3 N (by omega) order)
    (hReducing :
      ∀ (j : ℕ) (N : Matroid α),
        3 ≤ j →
        N.E.Finite →
        N.eRank = 3 →
        N.E.encard = ((3 * j : ℕ) : ℕ∞) →
        UniformlyDense N j →
        StrictlyUniformlyDense N j →
        (¬ ∃ e : α, e ∈ N.E ∧
          ∀ A : Set α, A ⊆ N.E →
            N.eRk A = 2 →
            A.ncard = 2 * j - 1 →
            e ∈ A) →
        ∃ D : Set α,
          N.IsBase D ∧
          HitsNearTightRankTwo N j D) :
    ∀ (k : ℕ) (M : Matroid α),
      0 < k →
      M.E.Finite →
      M.eRank = 3 →
      M.E.encard = ((3 * k : ℕ) : ℕ∞) →
      UniformlyDense M k →
      ∃ order : Fin (3 * k) ≃ M.E,
        CyclicBasisOrder3 M (by omega) order := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro M hk hE hRank hEcard hDense
      by_cases hkOne : k = 1
      · subst k
        simpa using
          exists_cyclicBasisOrder3_of_ground_encard_three
            M hE hRank (by simpa using hEcard)
      by_cases hkTwo : k = 2
      · subst k
        simpa using
          hTwo M hE hRank (by simpa using hEcard) hDense
      have hkThree : 3 ≤ k := by omega
      apply
        exists_cyclicBasisOrder3_of_strict_case
          M k hk hE hRank hEcard hDense
      intro hStrict
      have hLoopless : M.Loopless :=
        loopless_of_uniformlyDense M k hk hDense
      obtain ⟨D, hD, hHits⟩ : ∃ D : Set α,
          M.IsBase D ∧ HitsNearTightRankTwo M k D := by
        by_cases hCommon :
            ∃ e : α, e ∈ M.E ∧
              ∀ A : Set α, A ⊆ M.E →
                M.eRk A = 2 →
                A.ncard = 2 * k - 1 →
                e ∈ A
        · exact
            exists_isBase_hitsNearTight_of_common_point
              M k hLoopless hCommon
        · exact
            hReducing k M hkThree hE hRank hEcard
              hDense hStrict hCommon
      have hDelCard :
          (Matroid.delete M D).E.encard =
            ((3 * (k - 1) : ℕ) : ℕ∞) :=
        delete_ground_encard_eq_three_mul_pred
          M k hk hRank hEcard hD
      have hComplementCard :
          (M.E \ D).encard =
            ((3 * (k - 1) : ℕ) : ℕ∞) := by
        simpa using hDelCard
      have hDelRank :
          (Matroid.delete M D).eRank = 3 :=
        eRank_delete_eq_three_of_strict
          M k hkThree hRank hStrict hD
          hComplementCard
      have hDelDense :
          UniformlyDense (Matroid.delete M D) (k - 1) :=
        uniformlyDense_delete_of_strict_of_hitsNearTight
          M k hk hE hRank hDense hStrict hD
          hComplementCard hHits
      have hDelFinite :
          (Matroid.delete M D).E.Finite := by
        rw [Matroid.delete_ground]
        exact hE.subset Set.sdiff_subset
      obtain ⟨small, hsmall⟩ :=
        ih (k - 1) (by omega)
          (Matroid.delete M D) (by omega)
          hDelFinite hDelRank hDelCard hDelDense
      exact
        exists_cyclicBasisOrder3_of_cyclic_basis_deletion
          M k hkThree hRank hD hDelRank
          small hsmall

#print axioms Rank3KUM.rankThreeKUM_of_small_two_and_strict_deletion

end

end Rank3KUM
