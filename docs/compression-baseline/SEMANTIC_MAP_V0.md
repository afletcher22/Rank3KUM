# Semantic map v0 — interpretation layer

**Status:** AI interpretation of the mechanical dependency map. This file is not a kernel fact and
must not be used as evidence by itself that a declaration is important, redundant, or mathematically
equivalent to a paper step.

The underlying mechanical baseline is recorded in `MECHANICAL_MAP_SUMMARY.md`. The informal/formal
theorem boundary is frozen in `STATEMENT_CONTRACT.md`.

## Proposed semantic regions

### 1. Public theorem interface

Mechanical anchors:

- `Rank3KUM.UniformlyDense`
- `Rank3KUM.CyclicBasisOrder3`
- `Rank3KUM.cyclicIndex`
- `Rank3KUM.rankThreeKUM`

Interpretation: this is the statement surface rather than proof machinery. Compression should happen
underneath it. Changing its mathematical meaning would be statement drift.

### 2. Top-level induction and case dispatcher

Mechanical anchors:

- `Rank3KUM.rankThreeKUM_of_small_two_and_strict_deletion`
- `Rank3KUM.FinalReduction.exists_cyclicBasisOrder3_of_strict_case` (namespace-expanded Lean name
  `Rank3KUM.exists_cyclicBasisOrder3_of_strict_case`)
- `Rank3KUM.SmallCases`
- `Rank3KUM.Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural`

Interpretation: this region implements the paper's high-level skeleton. It separates `k = 1`,
`k = 2`, and `k >= 3`; for the general branch it dispatches between a proper nonempty tight set and
strict uniform density. The strict branch chooses a basis, deletes it, invokes strong induction, and
re-inserts it.

### 3. Tight-set reduction

Mechanical anchors/modules:

- `UniformDensity`
- `TightSetReduction`
- `TightFlatAutomatic`
- `ContractInterleave`
- `Interleave`
- `HalfWeave.Indexing`
- `HalfWeave.SortedBlocks`
- `HalfWeave.RankTwo`
- `HalfWeave.ParallelClasses`

Interpretation: this is the decomposition branch for equality in the density bound. Rank-one tight
flats are handled through contraction; rank-two tight flats through restriction; both ultimately use
rank-two cyclic-order machinery and interleaving.

Mechanical scale: the endpoint `exists_cyclicBasisOrder3_of_nonempty_proper_tight` has a
239-declaration project-local closure. Its rank-one and rank-two endpoints have closures of 213 and
215 declarations. Most of that shared footprint is rank-two enumeration/interleaving infrastructure,
not the two-case dispatcher itself.

### 4. Strict-density basis-selection geometry

Mechanical anchors/modules:

- `StrictDensity`
- `NearTightGeometry`
- `exists_isBase_hitsNearTight_of_strict_rankThree`
- `uniformlyDense_delete_of_strict_of_hitsNearTight`

Interpretation: this region makes deletion induction legal. Strict uniform density identifies the
near-tight rank-two obstructions; a basis is chosen to hit all of them; deleting that basis then
preserves the required density inequality with parameter `k - 1`.

Mechanical scale: the current hitting-basis endpoint has a 46-declaration closure, concentrated in
`NearTightGeometry` and `StrictDensity`. The deletion-density transport endpoint itself has a much
smaller 13-declaration closure.

### 5. Reinsertion / two-gap machinery

Mechanical anchors/modules:

- `InductionStep`
- `Splicing`
- `SpliceWrap`
- `CyclicRotate`
- all active `TwoGap/*` modules
- `TwoGap.universalTwoGapInsertion`

Interpretation: after induction supplies a cyclic basis order for the deletion, this region re-inserts
the deleted basis. `universalTwoGapInsertion` is the local mathematical engine; the surrounding
splicing modules translate that local result into the cyclic ordering used by the induction.

Mechanical scale: `universalTwoGapInsertion` has a 133-declaration project-local closure, while the
full deletion-to-reinsert endpoint `exists_cyclicBasisOrder3_of_cyclic_basis_deletion` has a
218-declaration closure.

### 6. Six-point base case

Mechanical anchors/modules:

- `Version2.SixPointStructural`
- `Version2.SixPointClassification`
- `Version2.SixPointMaximal`
- `Version2.SixPointPasch`
- `Version2.SixPointLemma9`
- `Version2.SixPointMatroidBridge`
- shared portions of `SixPointMatroid`

Interpretation: this is the active `k = 2` base-case proof. It encodes the structural linear-family
argument and translates an avoiding six-cycle into a matroid cyclic basis ordering.

The old `SixPointCombinatorics` certificate route is mechanically outside the main theorem closure.
`SixPointMatroid` remains partly active because the structural bridge reuses some of its matroid
geometry.

## Compiled but inactive v2 alternatives

The mechanical map independently recovers the distinction already documented in
`docs/V2_PAPER_LEAN_ALIGNMENT.md`:

- `Version2.HalfWeave` is outside the root closure;
- the revised `Version2.NearTight*` endpoint/classification route is outside the root closure;
- `Version2.ResidualSupportDisjoint` is outside the root closure;
- the version-2 structural six-point route is active.

This is an important proof-engineering mismatch, but **not statement drift**: the repository already
states explicitly that v2 was additive and that these checked alternatives were not all rewired into
`rankThreeKUM`.

## Comparison with the informal proof architecture

### Strong alignment

The formal dependency graph supports the claimed large-scale story:

`uniform density -> tight-or-strict -> (tight decomposition) or (strict deletion + induction + reinsertion)`.

The `k = 1` and `k = 2` base cases also appear exactly where the informal proof says they should.
The active `k = 2` route is the structural version-2 proof.

### Deliberate route mismatch

Three revised paper-level arguments have checked Lean counterparts but are not the path traversed by
the exported theorem:

1. largest-class-first rank-two ordering;
2. strengthened near-tight Lemma 8.8 / revised Proposition 8.11;
3. shared residual-support Lemma 7.20.

This matters for compression because merely deleting the legacy route would currently break the
exported theorem, while merely substituting the v2 endpoint may still retain much of the legacy
closure.

### No detected theorem-statement drift at this stage

`Challenge.lean` is byte-for-byte unchanged from the validated `palomar` branch, the substantive
project and Palomar wrapper both build, and Comparator remains the formal statement-equivalence
guard. The semantic map above changes no theorem statement.

## Initial compression hypotheses

These are hypotheses to test, not conclusions.

### A. Shared residual-support argument — first experiment

The paper has one conceptual Lemma 7.20 while the active two-gap route still reaches three specialized
residual-support disjointness proofs. This is the clearest mismatch between conceptual and active
formal structure.

Caveat: `Version2/ResidualSupportDisjoint.lean` currently imports the legacy
`TwoGap/EqualDisjointRest.lean`, so it cannot simply be imported back into those legacy files without
creating an import cycle. A real compression experiment should move the shared theorem, or the helper
lemmas it needs, to an earlier neutral module and make the three specializations thin corollaries.
The success criterion is a smaller active transitive closure, not merely fewer source lines.

### B. Near-tight revised route — second experiment

The stronger v2 classification is conceptually cleaner, but the v2 hitting-basis theorem still calls
several legacy `NearTightGeometry` helpers. Rewiring `FinalInduction` to the v2 endpoint may therefore
remove only part of the old route. The correct experiment is an ablation: substitute the revised
endpoint, regenerate the map, and measure which old declarations actually leave the root closure.
Only then decide whether the classification genuinely compresses the proof.

### C. Rank-two / HalfWeave — larger architectural experiment

The active tight-set machinery has a large rank-two footprint. The v2 `LargestFirstBlockModel`
clarifies that the weave proof needs only a largest-first condition, but
`cyclicRankTwoBasisOrderingOfUniformlyDense` currently constructs that weak model by first building
the legacy fully sorted enumeration and applying `ofSorted`. Therefore swapping to the existing v2
endpoint alone cannot eliminate the old sorting machinery.

A meaningful compression here requires constructing largest-first block data directly, rather than
using the fully sorted object as an implementation detail.

### D. Six-point legacy cleanup — useful but not primary structural compression

The old `SixPointCombinatorics` route is already outside the active theorem closure. Removing it from
the repository or root imports would reduce repository size and cognitive noise, but would not reduce
the active dependency closure of `rankThreeKUM`. Under the project's compression criterion this is
cleanup, not evidence of mathematical structural compression.

## Recommended order

1. shared residual-support rewiring;
2. regenerate and compare the mechanical map;
3. revised near-tight endpoint ablation/rewiring;
4. regenerate and compare;
5. direct largest-first rank-two construction;
6. only after active architecture stabilizes, delete or archive dead legacy routes and update the
   paper's proof-engineering notes.

At every stage the frozen `Challenge.lean` and Comparator check remain hard guards against formal
statement drift, while the paper statement contract is re-read when a change alters a major proof
interface.
