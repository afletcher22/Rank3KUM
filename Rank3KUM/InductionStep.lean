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
  have hlength :
      3 * (k - 1) + 3 = 3 * k := by
    omega
  rw [hlength] at order horder
  exact ⟨order, horder⟩

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_cyclic_basis_deletion

end

end Rank3KUM
