# Rank3KUM v2 paper–Lean alignment manifest

Status date: 2026-09-10

## Checked mathematical reference

The immutable Lean reference for the version-2 proof alignment is:

- commit `0c98e5cd9341a65f309e0d5d55907b8656c70e62` (`0c98e5c`);
- GitHub Actions CI run `34520738803`;
- clean root build: `Build completed successfully (3058 jobs)`;
- `Rank3KUM.rankThreeKUM` axiom dependencies: `propext`, `Classical.choice`, `Quot.sound`;
- `Rank3KUM.Version2.exists_cyclicBasisOrder3_of_strict_two_structural` has the same three dependencies;
- `Rank3KUM.Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural` has the same three dependencies.

In particular, the checked endpoint contains no `sorryAx` dependency.

Later commits on `version-2` that change README, handoff material, this manifest, or the paper-alignment tooling are documentation/tooling commits and do not replace `0c98e5c` as the mathematical reference unless Lean source is changed and re-audited.

## Revised arguments now represented in Lean

The following version-2 paper changes have checked Lean counterparts at `0c98e5c`:

| Paper item | Version-2 Lean correspondence | Alignment status |
|---|---|---|
| Proposition 4.2 | `Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense` | The largest parallel class need only be first; full sorting remains available in the legacy construction. |
| Lemma 5.1 | `Rank3KUM.Version2.isBase_insert_pair_of_indep_flat_rank3` | Wrapper matches the paper's distinct independent-pair formulation. |
| Lemma 6.3 | `Rank3KUM.Version2.isBase_insert_pair_of_contract_indep_rank3` | Wrapper matches the paper's independent-pair formulation after contraction. |
| Lemma 7.20 | `Rank3KUM/Version2/ResidualSupportDisjoint.lean` | The repeated residual-support disjointness argument is extracted into a shared version-2 lemma; legacy specialized consequences remain. |
| Lemmas 8.3–8.5 | `Rank3KUM/Version2/NearTightGeometry.lean` | Unrestricted distinct rank-two-flat geometry is packaged directly. |
| Lemma 8.8 | `Rank3KUM.Version2.nearTight_eq_one_of_nonconcurrent_three` | The strengthened no-fourth-near-tight-flat classification is checked. |
| Proposition 8.11 | `Rank3KUM.Version2.exists_isBase_hitsNearTight_of_strict_rankThree` | The paper's route through the strengthened Lemma 8.8 is checked. |
| Definition 9.1 | `Rank3KUM.Version2.LinearTripleFamily6` | Linear triple families are represented directly. |
| Lemma 9.2 | `Rank3KUM.Version2.exists_avoidingCycle6_of_linear` | The maximal-family proof, pair/Pasch classification, and the paper's two avoiding cycles are checked. |
| Section 9, `k = 2` | `Rank3KUM.Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural` | The structural six-point result is checked and is the active base-case route. |
| Theorem 1.2 | `Rank3KUM.rankThreeKUM` | `FinalInduction.lean` now calls the structural six-point theorem for `k = 2`. |

The earlier six-point finite certificate remains compiled for compatibility and as an independent fallback proof of the old conclusion. It is no longer the `k = 2` dependency used by `rankThreeKUM`.

## Paper text that must reflect this state

The aligned version-2 paper should no longer say that the revised Proposition 4.2, strengthened Lemma 8.8, Proposition 8.11 route, or structural Lemma 9.2 are awaiting formalization. The following locations are intentionally updated by `tools/update_v2_paper_alignment.py`:

1. the front-page formalization-status paragraphs;
2. the post-Lemma-8.8 formalization note;
3. the closing paragraph of Section 9;
4. the three formalization-status paragraphs in Section 11;
5. the acknowledgements paragraph;
6. the Appendix A introduction and immutable commit links; and
7. twelve Appendix A rows: Proposition 4.2, Lemmas 5.1, 6.3, 7.20, 8.3, 8.4, 8.5, 8.8, Proposition 8.11, Definition 9.1, Lemma 9.2, and the `k = 2` row.

The patcher deliberately does **not** rewrite the mathematical proofs or bibliography.

## Applying the paper patch

Run:

```bash
python3 tools/update_v2_paper_alignment.py Rank3KUM_paper_v2_draft.html
python3 tools/update_v2_paper_alignment.py Rank3KUM_paper_v2_draft.html Rank3KUM_paper_v2_aligned.html
```

The first command is validation-only. The second writes the aligned HTML. The script requires each targeted old paragraph and Appendix row exactly once, then checks that the principal stale formalization-status phrases and old `f956680` immutable source hash are absent from the result.

The repository CI syntax-checks the patcher with `python3 -m py_compile tools/update_v2_paper_alignment.py` before the Lean build.

## Scope boundary

Corollary 1.3 still invokes the external coprime-case theorem of van den Heuvel and Thomassé. That coprime ingredient is not formalized here. The checked claim in this repository remains the complete divisible rank-three case, with the full rank-three conclusion obtained mathematically by combining it with the published coprime theorem.
