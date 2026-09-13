# Rank3KUM compression statement contract

This file is the review contract used to prevent proof compression from drifting away from the
published mathematical claim.

## Informal theorem being preserved

Let `M` be a finite matroid of rank three whose ground set has cardinality `3k`, with `k > 0`.
Assume `M` is uniformly dense, meaning that every subset `X` of the ground set satisfies

`|X| <= k * r(X)`.

Then the ground set admits a cyclic ordering in which every three cyclically consecutive elements
form a basis of `M`.

This is the divisible rank-three theorem corresponding to Theorem 1.2 of the version-2 paper
*Cyclic basis orderings of uniformly dense rank-three matroids*, DOI
`10.5281/zenodo.22698709`.

## Formal statement surface

The frozen Palomar `Challenge.lean` defines:

```lean
def UniformlyDense (M : Matroid α) (k : ℕ) : Prop :=
  ∀ X : Set α, X ⊆ M.E →
    X.encard ≤ (k : ℕ∞) * M.eRk X


def cyclicIndex (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩


def CyclicBasisOrder3
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) : Prop :=
  ∀ i : Fin n,
    M.IsBase
      ({(σ i : α),
        (σ (cyclicIndex n hn i 1) : α),
        (σ (cyclicIndex n hn i 2) : α)} : Set α)
```

and advertises:

```lean
theorem rankThreeKUM
    (k : ℕ) (M : Matroid α) (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order
```

The substantive project theorem `Rank3KUM.rankThreeKUM` has the same hypotheses and conclusion using
the project-level versions of these definitions.

## Scope that must not drift

Compression must not silently strengthen or weaken any of the following:

- ambient rank is exactly three;
- the ground set is finite;
- its cardinality is exactly `3k` with `k > 0`;
- uniform density is required for every subset of the ground set;
- the conclusion is a cyclic enumeration of the entire ground set;
- every three cyclically consecutive elements form a basis;
- no simplicity, paving, representability, graphicness, or small-ground-set hypothesis is assumed.

The unrestricted KUM conjecture is not claimed here. The paper's all-cardinality rank-three corollary
also uses the external van den Heuvel--Thomasse nondivisible theorem and is not the theorem selected
for this compression experiment.

## Review rule

A change that preserves compilation but changes any item above is **statement drift**, not proof
compression. Such a change must not be accepted merely because Lean still proves the modified
statement.
