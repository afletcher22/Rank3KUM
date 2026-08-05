# Rank3KUM

A Lean 4 formalization of the **divisible case of the rank-three Kajitani–Ueno–Miyano
cyclic ordering theorem**.

## What is proved

A matroid `M` is *uniformly dense* if `|X| / r(X) ≤ |E| / r(M)` for every nonempty
`X ⊆ E` — no subset is denser than the ground set. A *cyclic basis ordering* is a cyclic
ordering of `E` in which every `r(M)` cyclically consecutive elements form a basis.
Kajitani, Ueno and Miyano conjectured in 1988 that a matroid has a cyclic basis ordering
if and only if it is uniformly dense. Necessity is easy; sufficiency is open in general.

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

where

- `UniformlyDense M k := ∀ X ⊆ M.E, X.encard ≤ (k : ℕ∞) * M.eRk X`
- `CyclicBasisOrder3 M hn σ := ∀ i, M.IsBase {σ i, σ (i+1), σ (i+2)}`, indices cyclic

With `r(M) = 3` and `|E| = 3k` the ratio `|E|/r(M)` equals `k`, so the hypothesis is
exactly the standard uniform-density condition.

There is **no** restriction to representable, paving, simple, graphic or small matroids.
Matroids with nontrivial parallel classes are covered.

## Scope

The theorem requires `3 ∣ |E|`. When `3 ∤ |E|` no `k` satisfies the cardinality
hypothesis, so the theorem is silent there rather than false. Rank three splits into
three cases:

| Case | Settled by |
|---|---|
| `3 ∤ \|E\|` | van den Heuvel–Thomassé, *JCTB* **102** (2012) 638–646 |
| `3 ∣ \|E\|`, `M` simple | McGuinness, *Electron. J. Combin.* **31**(4) (2024), Paper 4.9 |
| `3 ∣ \|E\|`, `M` not simple | **this development** |

`rankThreeKUM` covers the whole of `3 ∣ |E|`, simple or not, so combined with van den
Heuvel–Thomassé every finite uniformly dense rank-three matroid is cyclically orderable.
**That combination is a mathematical consequence, not a formalized one**: the coprime case
is quoted from the literature and is not machine-checked here. Formalizing it would first
require matroid union, which Mathlib does not currently provide.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and Mathlib revision
are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get   # download prebuilt Mathlib oleans
lake build
```

A clean build reports `Build completed successfully (3046 jobs)` with no errors and no
warnings. Building Mathlib from source instead of using the cache takes a few hours.

## Verification

```bash
# no incomplete or escape-hatch proofs
grep -rnE '\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b|native_decide' Rank3KUM/
```

The build prints axiom dependencies for the principal results. For the main theorem:

```
'Rank3KUM.rankThreeKUM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the standard Mathlib axioms. No mathematical hypothesis is introduced as an
axiom, and there are no `sorry`s, `admit`s, `unsafe` declarations, or uses of
`native_decide`. Two finite certificates appear in the six-element case: the
twenty-variable propositional core is discharged by an explicit decision tree (a
structured case analysis, not reflection), and small `Finset (Fin 6)` equalities use
`decide`, which evaluates in the Lean kernel. No external certificate or oracle is
trusted.

## Structure

The proof is a strong induction on `k`, organized by a dichotomy: either `M` has a
nonempty proper *tight* set (`|X| = k·r(X)`), or it is *strictly* uniformly dense.

| Module | Contents |
|---|---|
| `UniformDensity.lean` | Uniform density, tight sets, and their classification: a proper nonempty tight set is a flat of rank 1 (size `k`) or rank 2 (size `2k`) |
| `StrictDensity.lean` | Strict density, the dichotomy, near-tight sets, deletion transport |
| `CyclicOrder.lean` | `CyclicBasisOrder3` and cyclic index arithmetic |
| `HalfWeave/` | Cyclic orderings of rank-two matroids ("sorted enumerations") |
| `Interleave.lean`, `TightFlatAutomatic.lean` | The tight rank-two case, by restriction and interleaving |
| `ContractInterleave.lean`, `TightSetReduction.lean` | The tight rank-one case, by contraction |
| `TwoGap/` | The two-gap insertion theorem: of two adjacent gaps in a cycle, at least one admits a three-element basis |
| `Splicing.lean`, `SpliceWrap.lean` | Contiguous splicing built on two-gap insertion |
| `NearTightGeometry.lean` | Geometry of near-tight rank-two flats; existence of a basis hitting them all |
| `InductionStep.lean`, `FinalReduction.lean` | Deletion, induction, and case assembly |
| `SixPointCombinatorics.lean`, `SixPointMatroid.lean` | The `k = 2` base case and its finite certificate |
| `SmallCases.lean` | The `k = 1` base case |
| `FinalInduction.lean` | `rankThreeKUM` |

The largest single component is `TwoGap/`, which proves that if `D` is a basis and
`p, a, b, c, q` are five consecutive elements of a cycle with `{p,a,b}`, `{a,b,c}`,
`{b,c,q}` bases, then `D` can be inserted into the gap `a|b` or the gap `b|c` so that
every new window is a basis. It assumes only that the rank is three — no density,
simplicity, representability or finiteness.

## License

See `LICENSE`.
