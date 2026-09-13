import Rank3KUM.InductionStep

namespace Rank3KUM.Version2

open Set

noncomputable section

variable {α : Type*}

/--
The induction splice in the natural `3k` parametrization, with the arithmetic
identification `3(k-1)+3 = 3k` discharged directly.  This avoids introducing a
separate `Fin` transport equivalence and proving that it commutes with cyclic
indices.
-/
theorem exists_cyclicBasisOrder3_of_cyclic_basis_deletion_direct
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
  have hsplice :=
    Rank3KUM.contiguousBasisSplicing
      M hRank hD hDelRank
      (show 6 ≤ 3 * (k - 1) by omega)
      small hsmall
  have hlen : 3 * (k - 1) + 3 = 3 * k := by
    omega
  rw [hlen] at hsplice
  exact hsplice

#print axioms Rank3KUM.Version2.exists_cyclicBasisOrder3_of_cyclic_basis_deletion_direct

end

end Rank3KUM.Version2