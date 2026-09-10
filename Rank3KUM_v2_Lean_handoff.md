# Rank3KUM v2: checked paper-to-Lean handoff

This handoff supersedes the pre-alignment handoff prepared on 10 September 2026. The version-2 Lean alignment described below has now been implemented and checked on branch `version-2`.

## Checked reference

The immutable code reference for the completed alignment pass is:

`0c98e5cd9341a65f309e0d5d55907b8656c70e62`

CI run `34520738803` completed successfully with:

```text
Build completed successfully (3058 jobs).
```

The principal theorem and the two new structural six-point theorems print exactly the standard Mathlib axiom dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, the checked route contains no `sorryAx`. The existing project policy remains unchanged: no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` is required by the proof.

A later documentation-only commit may move the branch head. Paper source links should use the immutable checked code commit above unless the full paper is regenerated against a later code-equivalent checked commit.

## Status of the version-2 mathematical alignment

### Proposition 4.2 — aligned

The paper's largest-class-first half-weave proof is represented in:

- `Rank3KUM/Version2/HalfWeave.lean`
- `Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense`

The version-2 module weakens the construction to the paper's actual requirement: a largest parallel class is placed first; full sorting of the remaining classes is not logically required. The original sorted-enumeration development remains available and compiling.

### Lemmas 5.1 and 6.3 — correspondence wrappers added

`Rank3KUM/Version2/CorrespondenceWrappers.lean` records the small conversions needed to match the revised paper hypotheses and conclusions, including the independent-pair formulations. These were correspondence/statement-precision issues, not changes to the main theorem.

### Lemmas 8.3–8.5 — unrestricted geometry aligned

`Rank3KUM/Version2/NearTightGeometry.lean` supplies the revised rank-two-flat geometry without the old unnecessary equal-cardinality hypothesis where the paper states the unrestricted result. The original declarations remain intact for compatibility.

### Lemma 8.8 — stronger statement formalized

The strengthened statement that a nonconcurrent triple of near-tight rank-two flats exhausts the near-tight family for `k ≥ 3` is formalized as:

`Rank3KUM.Version2.nearTight_eq_one_of_nonconcurrent_three`

in `Rank3KUM/Version2/NearTightClassification.lean`.

The proof follows the revised incidence-count argument: a hypothetical fourth near-tight flat would meet the three chosen flats too often, giving the paper's incompatible lower and upper counts. The old avoidance theorem remains compiled but is no longer the only formal counterpart of Lemma 8.8.

### Proposition 8.11 — revised proof route formalized

The hitting-basis construction using the stronger Lemma 8.8 is formalized in:

`Rank3KUM/Version2/NearTightHitting.lean`

with principal declaration:

`Rank3KUM.Version2.exists_isBase_hitsNearTight_of_strict_rankThree`

The conclusion agrees with the existing theorem, but the version-2 route now mirrors the revised paper proof.

### Lemma 7.20 — shared residual-support argument extracted

`Rank3KUM/Version2/ResidualSupportDisjoint.lean` packages the common argument behind the three residual-support disjointness instances used in the paper's table. This is additive; the original specialized declarations are retained.

### Definition 9.1 and Lemma 9.2 — structural proof formalized

The version-2 Section 9 proof is now represented by the following modules:

- `Rank3KUM/Version2/SixPointStructural.lean`
- `Rank3KUM/Version2/SixPointClassification.lean`
- `Rank3KUM/Version2/SixPointMaximal.lean`
- `Rank3KUM/Version2/SixPointPasch.lean`
- `Rank3KUM/Version2/SixPointLemma9.lean`

The named definition

`Rank3KUM.Version2.LinearTripleFamily6`

formalizes Definition 9.1 directly. The development proves the point-degree bound, the incidence bound `|F| ≤ 4`, extension to an inclusion-maximal linear family, and the maximal-family dichotomy. Up to relabelling the maximal family is either

```text
{012,345}
```

or the Pasch family

```text
{012,034,135,245}.
```

The exact avoiding cycles used in the paper are checked:

```text
(0,1,3,2,4,5)
(0,1,4,2,3,5)
```

The structural version of Lemma 9.2 is:

`Rank3KUM.Version2.exists_avoidingCycle6_of_linear`.

All six windows of both displayed cycles are proved explicitly. The original eight-order finite certificate remains compiled as a legacy proof route, but it is no longer required by the active version-2 Section 9 argument.

### Section 9, `k = 2` — structural matroid bridge formalized and active

`Rank3KUM/Version2/SixPointMatroidBridge.lean` connects the abstract linear-family lemma to the strict six-element matroid case.

The bridge defines the actual family of bad three-subsets:

`badTripleFamily6`.

It proves linearity using only the geometric fact that two distinct bad triples cannot share a pair. The helper `exists_shared_pair_residuals_of_three_sets` extracts the common pair and residual vertices by cardinality, rather than by a six-point case table.

The avoiding cycle from Lemma 9.2 is converted to a single generic permutation of `Fin 6`, and its six windows are converted back to matroid bases. The principal declarations are:

- `Rank3KUM.Version2.exists_cyclicBasisOrder3_of_strict_two_structural`
- `Rank3KUM.Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural`

`Rank3KUM.rankThreeKUM` in `FinalInduction.lean` now invokes the second theorem in its `k = 2` callback. Thus the exported main theorem uses the structural Section 9 route, not `sixPointGoodAlternatives_of_linear`.

The old `SixPointMatroid.lean` remains imported because it contains the shared definitions `finSixSet`, `SixPointBad`, and the genuine geometric lemma `not_both_sixPointBad_of_shared_pair`. The large `LinearSixBad` certificate and eight-order selection theorem are retained for compatibility but are not dependencies of the active `k = 2` callback.

## What remains before the paper and repository are release-ready

The mathematical/Lean alignment requested for version 2 is complete at the checked commit above. The remaining work is editorial and release-oriented:

1. Update the paper's front-page formalization-status paragraphs, the end of §9, §11, and Appendix A so they no longer describe Proposition 4.2, Lemma 8.8, Proposition 8.11, or Lemma 9.2 as pending alignment.
2. Change Appendix A's comparison commit from `f956680` to the checked version-2 commit and regenerate immutable source links/line anchors against that commit.
3. Update the Appendix A rows for the new `Version2` declarations, especially Proposition 4.2, Lemmas 8.3–8.8, Proposition 8.11, Definition 9.1, Lemma 9.2, and the `k = 2` base case.
4. Update §11's build description from the old 3,046-job / finite-certificate account to the checked 3,058-job structural route.
5. Preserve the scope statement that Corollary 1.3 still invokes the external coprime-case theorem of van den Heuvel and Thomassé; only the divisible theorem is machine-checked here.
6. Render the revised HTML to PDF and visually inspect page breaks, tables, links, mathematical symbols, and Appendix A before release.
7. Do not publish a new Zenodo version or move a release tag without an explicit release decision. At upload time, recheck live Zenodo metadata, including the initials Á. Jánosik and B. Mátravölgyi.

## Attribution and scope notes retained from the review

Credit Sean McGuinness, *Cyclic Orderings of Paving Matroids*, §1.1 (arXiv:2308.12239v2), for deletion followed by contiguous insertion and the rank-three two-gap argument in the paving case. The paper may describe the present theorem as extending the method to arbitrary rank-three matroids, but should not make an unqualified priority claim that the local two-gap formulation itself is new.

Section 9's Kotlar–Ziv citation remains attribution/context only. Do not replace the self-contained six-point proof with a formalization of matroid partition, and do not claim prescribed-basis preservation.

Keep the pinned Lean toolchain unless a concrete compatibility issue requires a change. No broad cleanup or redesign is needed for the version-2 alignment pass.
