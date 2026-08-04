import Rank3KUM.Splicing

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
The induction splice in the natural `3k` parametrization: once deleting a
three-element basis leaves a cyclic order on `3(k-1)` elements, the two-gap
theorem inserts that basis and returns a cyclic order on all `3k` elements.
-/
theorem exists_cyclicBasisOrder3_of_cyclic_basis_deletion
    (M : Matroid α) (k : ℕ)
    (hk : 3 ≤ k)
    (hRank : M.eRank = 3)
    {D : Set α}
    (hD : M.IsBase D)
    (hDelRank : (Matroid.delete M D).eRank = 3)
    (small : Fin (3 * (k - 1)) ≃
      (Matroid.delete M D).E)
    (hsmall :
      CyclicBasisOrder3 (Matroid.delete M D)
        (by omega) small) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  obtain ⟨order, horder⟩ :=
    contiguousBasisSplicing
      M hRank hD hDelRank
      (show 6 ≤ 3 * (k - 1) by omega)
      small hsmall
  let castIndex :
      Fin (3 * k) ≃ Fin (3 * (k - 1) + 3) :=
    finCongr (by omega)
  let fullOrder : Fin (3 * k) ≃ M.E :=
    castIndex.trans order
  refine ⟨fullOrder, ?_⟩
  intro i
  have hcyclic (j : ℕ) :
      castIndex (cyclicIndex (3 * k) (by omega) i j) =
        cyclicIndex (3 * (k - 1) + 3) (by omega)
          (castIndex i) j := by
    apply Fin.ext
    simp [castIndex, cyclicIndex]
  have hi := horder (castIndex i)
  change M.IsBase
    ({(order (castIndex i) : α),
      (order (castIndex
        (cyclicIndex (3 * k) (by omega) i 1)) : α),
      (order (castIndex
        (cyclicIndex (3 * k) (by omega) i 2)) : α)} :
        Set α)
  rw [hcyclic 1, hcyclic 2]
  exact hi

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_cyclic_basis_deletion

end

end Rank3KUM
