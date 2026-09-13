# Rank3KUM semantic annotation of the mechanical proof map

**Status:** first AI semantic pass. No mathematical Lean source has been modified.

This is deliberately a second layer over the deterministic dependency map. Mechanical dependency
facts remain separate from the labels below. Every semantic label, architectural interpretation, or
attention signal in this file is a reviewable hypothesis rather than a kernel fact.

The root is `Rank3KUM.rankThreeKUM`. The frozen statement contract remains
`docs/compression-baseline/STATEMENT_CONTRACT.md`, and `Challenge.lean` remains the Palomar drift
guard. Palomar-specific packaging is not an optimization target.

## Important reading of the raw map

The active root closure contains 647 project-local constants, but only 283 are source-authored
declarations/data constructors; 364 are Lean-internal/elaboration-generated proof/helper constants.
The 647-node number therefore must not be read as 647 independently authored lemmas. Generated
constants are useful for kernel-structure measurements, but are not direct source-level compression
targets.

## Proposed semantic architecture

```text
Rank3KUM.rankThreeKUM
|
|-- k = 1 ----------------> direct three-element base case
|
|-- k = 2 ----------------> structural six-point route
|                            bad triples -> linear family
|                            -> maximal pair/Pasch classification
|                            -> avoiding six-cycle -> cyclic basis order
|
`-- k >= 3
    |
    `-- uniform density -> [proper nonempty tight] OR [strictly dense]
        |
        |-- tight
        |   |-- rank-1 tight flat -> contract to rank 2 -> half-weave -> interleave
        |   `-- rank-2 tight flat -> restrict to rank 2 -> half-weave -> interleave
        |
        `-- strict
            -> near-tight geometry chooses a basis hitting deletion obstructions
            -> delete basis; deletion remains rank 3 and uniformly dense with parameter k-1
            -> induction
            -> universal two-gap theorem + splicing reinserts deleted basis
```

This high-level architecture is supported directly by `FinalInduction.lean`, `FinalReduction.lean`,
`TightSetReduction.lean`, and the corresponding branch endpoints. The semantic map therefore agrees
with the informal tight/strict and delete-induct-reinsert story at the top level.

## Active semantic clusters

| ID | Modules | Label | Active constants | Authored | Generated | Interpretation |
|---|---|---|---:|---:|---:|---|
| S01 | `UniformDensity` | density / tight-set structure | 10 | 10 | 0 | Uniform density, tightness, looplessness, and classification of proper tight flats. |
| S02 | `CyclicOrder`, `CyclicRotate` | cyclic-order interface | 13 | 11 | 2 | `cyclicIndex`, `CyclicBasisOrder3`, append/delete and rotation transport. This carries part of the public theorem meaning. |
| S03 | `HalfWeave.Indexing`, `HalfWeave.SortedBlocks`, `HalfWeave.ParallelClasses`, `HalfWeave.RankTwo` | rank-two half-weave engine | 140 | 84 | 56 | Partition a rank-two ground set into singleton-closure/parallel classes, fully sort them, flatten coordinates, weave, and prove every successor pair is a basis. |
| S04 | `Interleave`, `TightFlatAutomatic` | tight rank-two gluing | 64 | 30 | 34 | Restrict to a tight rank-two flat, obtain its rank-two cyclic ordering, interleave the `k` complementary points with the `2k` flat elements, and verify all rank-three cyclic windows. |
| S05 | `ContractInterleave` | tight rank-one contraction / gluing | 19 | 9 | 10 | Contract a tight rank-one flat to rank two, solve the contraction with the same half-weave engine, then interleave the contracted class back. |
| S06 | `TightSetReduction` | tight-branch dispatcher | 2 | 1 | 1 | Classify a proper tight flat as rank one or rank two and dispatch to S05 or S04. |
| S07 | `TwoGap*` | universal two-gap insertion engine | 133 | 51 | 82 | Local rank-three insertion theorem via symmetric basis exchange, blocked-gap singleton reductions, and equal/unequal singleton-partner contradictions. |
| S08 | `Splicing`, `SpliceWrap` | delete / reinsert splicing adapter | 66 | 2 | 64 | Apply the two-gap theorem to five consecutive elements at a cyclic cut and verify the wrap-around windows after inserting the deleted basis. |
| S09 | `StrictDensity` | strict-density deletion criteria | 24 | 15 | 9 | Define strict density and near-tight obstructions; prove that a basis hitting every near-tight rank-two set gives a rank-preserving uniformly dense deletion. |
| S10 | `NearTightGeometry` | near-tight hitting-basis geometry | 33 | 10 | 23 | Analyze intersections of near-tight rank-two flats and construct a basis hitting every near-tight obstruction. |
| S11 | `InductionStep` | strict induction step | 8 | 2 | 6 | Convert the cyclic order of a rank-preserving deletion on `3(k-1)` elements into the `3k` order by splicing. |
| S12 | `FinalReduction` | global tight / strict reduction | 2 | 1 | 1 | Exhaustive split: proper nonempty tight set versus strict uniform density. |
| S13 | `SmallCases` | `k = 1` base case | 5 | 1 | 4 | Direct three-element case. |
| S14 | `SixPointMatroid` | six-point shared matroid geometry | 13 | 5 | 8 | Shared bad-triple and strict-`k=2` matroid facts; the same historical file also contains inactive legacy-certificate material. |
| S15 | `Version2.SixPointStructural`, `SixPointClassification`, `SixPointMaximal`, `SixPointPasch`, `SixPointLemma9` | six-point structural combinatorics | 83 | 32 | 51 | Linear triple families, maximal extension, pair/Pasch classification, and existence of an avoiding six-cycle. |
| S16 | `Version2.SixPointMatroidBridge` | six-point matroid bridge | 25 | 17 | 8 | Turn actual dependent triples into a linear family, apply the avoiding-cycle result, and translate back to a cyclic basis ordering. |
| S17 | `FinalInduction` | final induction / orchestration | 7 | 2 | 5 | Strong induction on `k`; uses direct `k=1`, structural `k=2`, and for `k>=3` the global tight/strict reduction, with recursion only on the strict branch. |

## Interpretation notes

### S01/S06: the tight split is mathematical, not ambient lower-rank KUM

The rank-one/rank-two labels refer to the rank of a proper tight flat inside the ambient rank-three
matroid. The tight dispatcher itself is tiny; most formal mass lies in the shared rank-two engine and
the two gluing realizations below it.

### S03: the rank-two representation is the deepest active formal cluster

S03 reaches root depth 12. The active route explicitly sorts all parallel/singleton-closure classes,
constructs finite sigma coordinates and prefix sums, proves block monotonicity and fiber-cardinality
facts, and then applies the half-weave indexing equivalence. This is a strong *attention signal* for
later compression, not a conclusion that the mathematics is redundant.

### S04/S05: two geometrically different reductions converge on one rank-two engine

The rank-two tight branch uses restriction; the rank-one tight branch uses contraction. These are
mathematically distinct reductions, but after reduction they both use the same HalfWeave machinery
and the same one-two interleaving idea. A later review can ask whether this commonality supports a
more abstract gluing interface without pretending restriction and contraction are the same argument.

### S07: conceptually compact endpoint, substantial internal contradiction tree

`universalTwoGapInsertion` is a clean standalone rank-three theorem with no density, simplicity,
paving, representability, or finiteness assumption. Its active proof underneath is much larger:
partner sets, support/residual-support lemmas, and separate equal/unequal singleton-partner
contradictions. Whether that case tree reflects irreducible mathematics or current proof shape is a
question for later experiments, not settled by the graph.

### S08: raw node count badly overstates source-level complexity

S08 has 66 active constants but only two source-authored declarations. Most of its kernel graph is
elaboration-generated proof structure from `contiguousBasisSplicing` and the wrap theorem. This is a
concrete example of why source size or raw declaration count alone is a poor compression objective.

### S09/S10: useful abstraction boundary in the strict branch

S09 says what a deletion-preserving basis must accomplish: hit every near-tight rank-two obstruction.
S10 is the geometry proving such a basis exists. The split therefore looks semantically meaningful:
"deletion obstruction criterion" versus "basis-selection geometry."

### S14-S16: structural six-point route is genuinely active

The v2 structural route is not merely compiled in parallel: it lies in the root closure and is the
`k=2` base-case route supplied to the strong induction. The old finite-certificate combinatorics is
outside the root closure, although shared matroid lemmas in `SixPointMatroid.lean` remain active.

## Checked alternatives outside the active root closure

These are unusually valuable for compression because they give formally checked alternate
representations of informal proof steps rather than requiring an AI to invent replacements from
scratch.

| ID | Region | Outside-root constants | Status and relevance |
|---|---|---:|---|
| A01 | `Version2.HalfWeave` | 85 | Paper-v2 Proposition 4.2: largest-class-first rank-two construction. Compiled, but `rankThreeKUM` still reaches the older fully sorted S03 route. |
| A02 | `Version2.NearTightGeometry`, `NearTightClassification`, `NearTightHitting` | 16 | Revised Lemma 8.8 / Proposition 8.11 route. Compiled, but the root still reaches original S10. |
| A03 | `Version2.ResidualSupportDisjoint` | 6 | Shared Lemma 7.20 residual-support disjointness theorem. Compiled, while active S07 still reaches the specialized residual-support consequences. |
| A04 | `Version2.CorrespondenceWrappers` | 4 | Paper-correspondence wrappers; useful for alignment checks, not necessarily an active-proof target. |
| A05 | `SixPointCombinatorics` | 27 | Legacy finite-certificate route; already superseded by active S15/S16, retained as checked fallback/history. |

The v2 paper-Lean alignment manifest explicitly records A01-A03 as checked-but-inactive and the
structural six-point route as active. Therefore these are not presently *undisclosed* paper/Lean
drift; they are deliberate proof-correspondence mismatches that need to stay explicit.

## Formal map versus informal/paper architecture

The first comparison yields four conclusions.

1. **Top-level architecture agrees.** The formal theorem really does implement separate `k=1` and
   `k=2` base cases, the tight/strict dichotomy, and the strict delete-induct-reinsert route.
2. **The tight branch is structurally real but implementation-heavy.** Its dispatcher is tiny; its
   mass is the rank-two HalfWeave plus restriction/interleaving and contraction/interleaving.
3. **Three v2 simplifications are checked but not active.** A01, A02, and A03 are exactly the places
   where the paper has cleaner checked formulations that have not yet replaced the root's legacy
   dependencies.
4. **The six-point rewrite is active.** Here the paper-v2 structural presentation and exported Lean
   dependency route are already much closer.

## Drift watchlist

Every compression experiment should re-check all of the following.

- `UniformlyDense`, `cyclicIndex`, `CyclicBasisOrder3`, and the hypotheses/conclusion of
  `rankThreeKUM` must continue to agree with the frozen Palomar Challenge and paper Theorem 1.2.
- Ambient rank remains exactly three; the ground set remains finite and of size exactly `3k`,
  `k>0`; uniform density remains quantified over every ground-set subset; no simplicity, paving,
  representability, graphicness, or small-ground-set hypothesis may silently appear.
- The machine-checked claim remains the divisible rank-three theorem. The nondivisible
  van den Heuvel--Thomasse ingredient remains external.
- If A01 replaces S03, correspondence text should move from "compiled alternative" to "active"
  only after a regenerated dependency map proves the change.
- Apply the same rule if A02 replaces S10 or A03 replaces the specialized S07 dependencies.
- Preserve the present fact that the structural six-point route is active unless a later explicit
  design decision changes it.
- A proof architecture change that still compiles can nevertheless create informal/formal drift;
  the paper correspondence must be re-audited after each accepted structural rewrite.

## Questions for adversarial review

Astra should specifically challenge these labels rather than taking them as ground truth:

- Is S03 really one semantic engine, or should parallel-class representation and the half-weave
  theorem be separated more sharply?
- Are S04 and S05 legitimately two realizations of a common tight-flat gluing principle, or does
  that description over-unify restriction and contraction?
- Is S07's equal/unequal singleton-partner tree mathematically intrinsic to two-gap insertion, or
  primarily an artifact of the current proof?
- Is the S09/S10 boundary the right abstraction boundary for the strict branch?
- Should active shared lemmas in `SixPointMatroid.lean` be separated more aggressively from the
  inactive historical certificate route in the same file?
- Does the actual published v2 paper, not merely the alignment manifest, accurately state that
  A01/A02/A03 are checked but inactive and that S15/S16 are active?

No compression or deletion decision is made by this document.
