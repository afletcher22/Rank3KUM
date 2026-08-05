# Rank3KUM

A Lean 4 formalization of the **divisible case of the rank-three Kajitani–Ueno–Miyano cyclic ordering theorem**, developed under the direction of Austen Fletcher with GPT-5.6 Sol and Claude Opus 5.

[![Paper DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21813716.svg)](https://doi.org/10.5281/zenodo.21813716)
[![Formalization DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21813155.svg)](https://doi.org/10.5281/zenodo.21813155)

- **Paper:** [*Cyclic basis orderings of uniformly dense rank-three matroids*](https://doi.org/10.5281/zenodo.21813716)
- **Archived formalization:** [Rank3KUM v1.0.0](https://doi.org/10.5281/zenodo.21813155)

## What is proved

A matroid `M` is *uniformly dense* if

```text
|X| / r(X) ≤ |E| / r(M)
```

for every nonempty `X ⊆ E`; equivalently, no subset is denser than the ground set.

A *cyclic basis ordering* is a cyclic ordering of `E` in which every `r(M)` cyclically consecutive elements form a basis.

Kajitani, Ueno and Miyano conjectured in 1988 that a matroid has a cyclic basis ordering if and only if it is uniformly dense. Necessity is immediate; sufficiency remains open in general.

This repository proves sufficiency for rank three when `|E|` is divisible by three.

```lean
theorem Rank3KUM.rankThreeKUM
    (k : ℕ) (M : Matroid α) (hk : 0 < k)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    (hDense : UniformlyDense M k) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order
```

Here,

- `UniformlyDense M k := ∀ X ⊆ M.E, X.encard ≤ (k : ℕ∞) * M.eRk X`;
- `CyclicBasisOrder3 M hn σ` means that `{σ i, σ (i + 1), σ (i + 2)}` is a basis for every `i`, with indices interpreted cyclically.

When `r(M) = 3` and `|E| = 3k`, the ratio `|E| / r(M)` equals `k`, so the hypothesis is exactly the standard uniform-density condition.

There is **no restriction** to representable, paving, simple, graphic or small matroids. Matroids with nontrivial parallel classes are included.

## Scope

The theorem requires `3 ∣ |E|`. When `3 ∤ |E|`, no `k` satisfies the cardinality hypothesis, so the theorem is silent in that case rather than false.

Rank three divides into three cases:

| Case | Settled by |
|---|---|
| `3 ∤ |E|` | van den Heuvel–Thomassé, *J. Combin. Theory Ser. B* **102** (2012), 638–646 |
| `3 ∣ |E|`, `M` simple | McGuinness, *Electron. J. Combin.* **31**(4) (2024), Paper 4.9 |
| `3 ∣ |E|`, `M` not simple | **This development** |

`rankThreeKUM` covers the entire divisible case `3 ∣ |E|`, whether or not `M` is simple. Combined with the theorem of van den Heuvel and Thomassé, it follows that every finite uniformly dense rank-three matroid is cyclically orderable.

**That combined conclusion is a mathematical consequence, not a fully formalized theorem in this repository.** The coprime case is quoted from the literature and is not machine-checked here. Formalizing the published coprime-case proof would require additional infrastructure, including a suitable formalization of the relevant matroid-union machinery, and lies outside the scope of this development.

## Building

The project requires [elan](https://github.com/leanprover/elan). The Lean toolchain and exact Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

The first command downloads prebuilt Mathlib `.olean` files. A clean build reports:

```text
Build completed successfully (3046 jobs).
```

The build completes with no errors and no warnings. Building Mathlib from source instead of using the cache may take several hours.

## Verification

The development contains no incomplete proofs or escape hatches.

```bash
grep -rnE '\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b|native_decide' Rank3KUM/
```

The build prints the axiom dependencies of the principal results. For the main theorem:

```text
'Rank3KUM.rankThreeKUM' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are the standard Mathlib axioms. No mathematical hypothesis is introduced as an axiom.

The repository contains:

- no `sorry`;
- no `admit`;
- no custom `axiom` declarations;
- no `unsafe` declarations;
- no use of `native_decide`.

Two finite certificates occur in the six-element base case. The twenty-variable propositional core is discharged by an explicit decision tree: a structured case analysis rather than reflection. Small `Finset (Fin 6)` equalities use `decide`, which evaluates inside the Lean kernel. No external certificate, SAT solver or untrusted oracle is used by the checked proof.

## Proof structure

The proof is a strong induction on `k`, organized by the following dichotomy:

1. `M` has a nonempty proper *tight* set satisfying `|X| = k · r(X)`; or
2. `M` is *strictly* uniformly dense.

A nonempty proper tight set in rank three is shown to be a flat of one of two kinds:

- rank one and size `k`;
- rank two and size `2k`.

The rank-two tight case is handled by restricting to the tight flat, constructing a cyclic rank-two ordering, and interleaving the remaining elements.

The rank-one tight case is handled by contracting the tight parallel class, constructing a cyclic ordering in the resulting rank-two matroid, and lifting it by interleaving.

In the strictly dense case, a carefully selected basis is deleted. The resulting matroid remains uniformly dense, so induction applies. The deleted basis is then reinserted using the universal two-gap insertion theorem.

## Structure

| Module | Contents |
|---|---|
| `UniformDensity.lean` | Uniform density, tight sets, looplessness and classification of proper nonempty tight sets |
| `StrictDensity.lean` | Strict density, the tight/strict dichotomy, near-tight sets and deletion transport |
| `CyclicOrder.lean` | `CyclicBasisOrder3` and cyclic index arithmetic |
| `HalfWeave/` | Cyclic orderings of rank-two matroids through sorted enumerations |
| `Interleave.lean` | The one-two interleaving construction |
| `TightFlatAutomatic.lean` | The tight rank-two case by restriction and interleaving |
| `ContractInterleave.lean` | Rank transfer and interleaving after contraction |
| `TightSetReduction.lean` | Assembly of the two tight-set cases |
| `TwoGap/` | The universal two-gap insertion theorem |
| `Splicing.lean`, `SpliceWrap.lean` | Contiguous insertion of a deleted basis into a cyclic ordering |
| `NearTightGeometry.lean` | Geometry of near-tight rank-two flats and construction of a basis meeting all of them |
| `InductionStep.lean` | Deletion, induction and reinsertion |
| `FinalReduction.lean` | Reduction of the strict case to the induction step |
| `SixPointCombinatorics.lean` | Finite combinatorial certificate for the six-element case |
| `SixPointMatroid.lean` | Translation of the finite certificate into the `k = 2` matroid theorem |
| `SmallCases.lean` | The `k = 1` base case |
| `FinalInduction.lean` | Strong induction and the theorem `rankThreeKUM` |

## The two-gap theorem

The largest individual component is `TwoGap/`.

Suppose `D` is a basis and

```text
p, a, b, c, q
```

are five distinct elements outside `D` such that

```text
{p, a, b}, {a, b, c}, {b, c, q}
```

are bases.

The two-gap theorem proves that `D` can be inserted into at least one of the two neighboring gaps

```text
a | b
```

or

```text
b | c
```

in some ordering of the elements of `D`, so that every newly created three-element window is a basis.

The theorem assumes only that the ambient matroid has rank three. It does not assume uniform density, finiteness, simplicity, representability or paving.

Its principal Lean declaration is:

```lean
Rank3KUM.TwoGap.universalTwoGapInsertion
```

## Formalization and computational assistance

Under the direction of Austen Fletcher, the mathematical argument was developed primarily by GPT-5.6 Sol.

The Lean 4 formalization and preparation of the accompanying paper were produced collaboratively by GPT-5.6 Sol and Claude Opus 5, also under Fletcher's direction.

All formal claims in this repository are checked by Lean's kernel under the axiom dependencies listed above.

## Paper

The accompanying paper is:

> Austen Fletcher, *Cyclic basis orderings of uniformly dense rank-three matroids*, Carbon Silicon Labs, 2026.  
> DOI: [10.5281/zenodo.21813716](https://doi.org/10.5281/zenodo.21813716)

The paper gives a conventional mathematical presentation of the proof, explains the relation to prior work, and provides a cross-reference between numbered statements and their corresponding Lean declarations and source files.

## Citation

To cite the paper:

```bibtex
@article{Fletcher2026Rank3KUM,
  author      = {Austen Fletcher},
  title       = {Cyclic basis orderings of uniformly dense rank-three matroids},
  institution = {Carbon Silicon Labs},
  year        = {2026},
  doi         = {10.5281/zenodo.21813716},
  url         = {https://doi.org/10.5281/zenodo.21813716}
}
```

To cite the archived Lean formalization:

```bibtex
@software{Fletcher2026Rank3KUMLean,
  author  = {Austen Fletcher},
  title   = {Rank3KUM: Lean 4 formalization of the divisible rank-three
             Kajitani--Ueno--Miyano theorem},
  version = {1.0.0},
  year    = {2026},
  doi     = {10.5281/zenodo.21813155},
  url     = {https://doi.org/10.5281/zenodo.21813155}
}
```

The repository archive is available at:

[https://doi.org/10.5281/zenodo.21813155](https://doi.org/10.5281/zenodo.21813155)

## License

See [`LICENSE`](LICENSE).
