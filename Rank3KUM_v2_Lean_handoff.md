# Rank3KUM v2: checked paper-to-Lean handoff

This handoff supersedes the pre-alignment handoff prepared on 10 September 2026. The version-2 Lean alignment described below has been implemented and checked on branch `version-2`, and the corresponding paper-status edits have been prepared as a reproducible patch.

## Checked mathematical reference

The immutable mathematical code reference for the completed Lean pass is:

`0c98e5cd9341a65f309e0d5d55907b8656c70e62`

CI run `34520738803` completed successfully with:

```text
Build completed successfully (3058 jobs).
```

The principal theorem and the two structural six-point endpoint theorems print exactly the standard Mathlib axiom dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency. The project continues to use no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` in the proof.

Later documentation/tooling commits move the branch head. Paper source links should continue to use the immutable checked mathematical commit above unless Lean source is changed and re-audited.

## Important dependency distinction

The version-2 work is largely additive. Several cleaner paper arguments now have checked Lean counterparts, but most have **not** replaced the corresponding dependencies of `Rank3KUM.rankThreeKUM`.

Specifically:

- the largest-class-first rank-two construction is compiled, while the main theorem still follows the original rank-two route;
- the stronger Lemma 8.8 and revised Proposition 8.11 route are compiled, while the main theorem still follows the original near-tight route;
- the shared Lemma 7.20 residual-support argument is compiled, while the original three specialized residual-support results remain the dependencies of the two-gap route;
- the structural Section 9 proof is both compiled and active: the `k = 2` branch of `rankThreeKUM` now calls it.

The paper and Appendix A should therefore distinguish “checked counterpart” from “actual dependency of the exported theorem.” No further rewiring is required for publication.

## Status of the version-2 mathematical alignment

### Definition 4.1 and Proposition 4.2 — aligned

`Rank3KUM/Version2/HalfWeave.lean` now contains the paper-level output interface

`Rank3KUM.Version2.HalfWeave.CyclicRankTwoBasisOrdering`.

It packages an equivalence

```text
Fin k × Bool ≃ M.E
```

with the requirement that every `weaveNext` successor pair is a basis. This directly corresponds to Definition 4.1 rather than exposing only the sorted block input structure.

The same module contains

`Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense`,

which formalizes the paper's largest-class-first Proposition 4.2 construction. The remaining parallel classes do not need to be fully sorted. The legacy fully sorted construction remains compiled and is still the route reached by the main theorem's existing rank-two machinery.

### Lemmas 5.1 and 6.3 — correspondence wrappers added

`Rank3KUM/Version2/CorrespondenceWrappers.lean` records the small conversions needed to match the revised paper hypotheses and conclusions, including the independent-pair formulations. These were statement-correspondence issues, not changes to the main theorem.

### Lemmas 8.3–8.5 — unrestricted geometry aligned

`Rank3KUM/Version2/NearTightGeometry.lean` supplies the revised rank-two-flat geometry without the old unnecessary equal-cardinality hypothesis.

For Lemma 8.5, the new theorem

`Rank3KUM.Version2.inter_subset_closure_singleton_of_distinct_rankTwo_flats`

is the unrestricted closure statement. The paper's general cardinality consequence for arbitrary distinct rank-two flats under strict density is **derived** from this closure inclusion together with the Lemma 3.2 rank-one/parallel-class bound, represented in Lean by `StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one`. The older theorem `ncard_inter_le_k_sub_one_of_distinct_nearTight` is near-tight-specific and should not be presented as the general cardinality correspondence.

### Lemma 8.8 — stronger statement formalized

The strengthened statement that a nonconcurrent triple of near-tight rank-two flats exhausts the near-tight family for `k ≥ 3` is formalized as

`Rank3KUM.Version2.nearTight_eq_one_of_nonconcurrent_three`

in `Rank3KUM/Version2/NearTightClassification.lean`.

The proof follows the revised incidence-count argument. The original weaker avoidance theorem remains compiled and remains the result reached by the main theorem's existing near-tight route.

### Proposition 8.11 — revised proof route formalized

`Rank3KUM/Version2/NearTightHitting.lean` contains

`Rank3KUM.Version2.exists_isBase_hitsNearTight_of_strict_rankThree`.

This checks the paper's hitting-basis construction using the stronger Lemma 8.8. The original theorem with the same conclusion remains the dependency reached by `rankThreeKUM`.

### Lemma 7.20 — shared residual-support argument extracted

`Rank3KUM/Version2/ResidualSupportDisjoint.lean` contains the common theorem

`Rank3KUM.Version2.residualSupport_disjoint_of_shared_bridge`.

It packages the shared argument behind the three paper instances. This is additive: the original three specialized residual-support theorems remain compiled and remain the dependencies used by the existing two-gap route.

### Definition 9.1 and Lemma 9.2 — structural proof formalized

The version-2 Section 9 proof is represented by:

- `Rank3KUM/Version2/SixPointStructural.lean`
- `Rank3KUM/Version2/SixPointClassification.lean`
- `Rank3KUM/Version2/SixPointMaximal.lean`
- `Rank3KUM/Version2/SixPointPasch.lean`
- `Rank3KUM/Version2/SixPointLemma9.lean`

`Rank3KUM.Version2.LinearTripleFamily6` formalizes Definition 9.1 directly. The development proves the point-degree bound, the incidence bound `|F| ≤ 4`, extension to an inclusion-maximal linear family, and the maximal-family dichotomy. Up to relabelling, the maximal family is either

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

The structural version of Lemma 9.2 is

`Rank3KUM.Version2.exists_avoidingCycle6_of_linear`.

All six windows of both displayed cycles are proved explicitly. The original eight-order finite certificate remains compiled as a legacy proof route.

### Section 9, `k = 2` — structural matroid bridge formalized and active

`Rank3KUM/Version2/SixPointMatroidBridge.lean` connects the abstract linear-family lemma to the strict six-element matroid case.

It defines `badTripleFamily6`, proves that family linear from the genuine geometric fact that two distinct bad triples cannot share a pair, obtains an avoiding cycle from Lemma 9.2, and converts it to a cyclic basis ordering. The principal endpoint is

`Rank3KUM.Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural`.

`Rank3KUM.rankThreeKUM` in `FinalInduction.lean` now invokes this theorem in its `k = 2` callback. Thus the exported theorem's six-point route is structural rather than certificate-selected.

The old `SixPointMatroid.lean` remains imported because it contains shared definitions and genuine geometric infrastructure. The large `LinearSixBad` certificate and eight-order selection theorem remain compiled for compatibility but are no longer dependencies of the active `k = 2` callback.

## Paper-alignment tooling

The repository contains:

- `tools/update_v2_paper_alignment.py`, a narrow patcher for `Rank3KUM_paper_v2_draft.html`;
- `docs/V2_PAPER_LEAN_ALIGNMENT.md`, the audit manifest for the checked commit and affected Appendix A rows; and
- a CI step running `python3 -m py_compile tools/update_v2_paper_alignment.py` before the Lean build.

The patcher updates only the formalization-status/meta layer and affected Appendix correspondences. It does not rewrite the mathematical proof body or bibliography. It covers:

1. the front formalization-status paragraphs;
2. the post-Lemma-8.8 status note;
3. the closing paragraph of §9;
4. §11's build, decision-procedure, and correspondence paragraphs;
5. acknowledgements;
6. Appendix A's checked-commit introduction and immutable source hashes; and
7. thirteen changed Appendix rows: Definition 4.1; Proposition 4.2; Lemmas 5.1, 6.3, 7.20, 8.3, 8.4, 8.5, 8.8; Proposition 8.11; Definition 9.1; Lemma 9.2; and the `§9, k = 2` row.

`replace_row` now counts **all** matching rows before replacement and fails unless there is exactly one, so a duplicated target row cannot silently pass validation.

## What remains before release

The mathematical/Lean alignment is complete. The remaining work is artifact/release-oriented:

1. Apply `tools/update_v2_paper_alignment.py` to the actual self-contained `Rank3KUM_paper_v2_draft.html` source and retain the aligned HTML.
2. Render the aligned HTML to PDF and visually inspect page breaks, tables, links, mathematical symbols, and Appendix A.
3. Verify every immutable Appendix link against `0c98e5c` and adjust obsolete line fragments if necessary.
4. Perform a final textual search for stale statements such as `3,046 jobs`, `not yet been formalized`, `remain to be aligned`, and language implying that every compiled v2 counterpart is an active dependency of `rankThreeKUM`.
5. Keep the scope statement that Corollary 1.3 invokes the external coprime-case theorem of van den Heuvel and Thomassé; only the divisible theorem is machine-checked here.
6. Do not publish a new Zenodo version or move a release tag without an explicit release decision. At upload time, recheck live Zenodo metadata, including the initials Á. Jánosik and B. Mátravölgyi.

The current ChatGPT File Library copy of the HTML is readable for audit but is not a writable repository file, so the prepared patch has not been described as already applied to that artifact.

## Repository-size qualification

The version-2 Lean pass is an expository/proof-correspondence simplification, not a source-size reduction. It adds roughly a few thousand lines of version-2 Lean while retaining the older machinery. That is acceptable for this revision; no cleanup pass is recommended before publication.

## Attribution and scope notes retained from the review

Credit Sean McGuinness, *Cyclic Orderings of Paving Matroids*, §1.1 (arXiv:2308.12239v2), for deletion followed by contiguous insertion and the rank-three two-gap argument in the paving case. The paper may describe the present theorem as extending the method to arbitrary rank-three matroids, but should not make an unqualified priority claim that the local two-gap formulation itself is new.

Section 9's Kotlar–Ziv citation remains attribution/context only. Do not replace the self-contained six-point proof with a formalization of matroid partition, and do not claim prescribed-basis preservation.

Keep the pinned Lean toolchain unless a concrete compatibility issue requires a change. No broad cleanup or redesign is needed for the version-2 alignment pass.
