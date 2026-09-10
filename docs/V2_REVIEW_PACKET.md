# Rank3KUM Version 2 — reviewer packet

Date: 10 September 2026

This note is intended for an independent reviewer (Astra, Fable, or another model) who does not have the full development history. It separates the checked mathematical reference from later documentation/tooling work and highlights the few places where the version-2 paper proof and the exported Lean theorem intentionally use different checked routes.

## What to review

Please review together:

- `Rank3KUM_paper_v2_draft-update.pdf` (19 pages), generated from `Rank3KUM_paper_v2_draft-update.html`;
- GitHub repository `afletcher22/Rank3KUM`, branch `version-2`;
- this note.

The paper update is derived from the previously reviewed v2 draft. Its mathematical body and bibliography were not rewritten in the artifact-alignment pass; the changes are to formalization-status prose, immutable source links, and Appendix A correspondence rows.

## Fixed mathematical reference

The immutable Lean commit used by the paper is:

`0c98e5cd9341a65f309e0d5d55907b8656c70e62` (`0c98e5c`).

At that commit:

- the root build completed successfully with **3,058 jobs**;
- `Rank3KUM.rankThreeKUM` prints exactly the axiom dependencies `propext`, `Classical.choice`, and `Quot.sound`;
- the two structural six-point endpoint theorems print the same three dependencies;
- there is no `sorryAx` dependency;
- the active `k = 2` callback of `rankThreeKUM` is the new structural six-point theorem.

The later `version-2` commits through `6801af93775671ca6545e8da2231fb3b1286e998` are documentation/tooling only relative to `0c98e5c`; a GitHub compare showed no Lean-source changes. CI run `34527449570` at `6801af9` passed the strengthened paper-tooling checks and the full Lean build.

## Important dependency distinction

Do not infer that every cleaner version-2 proof has been rewired into the exported theorem.

The following **new version-2 counterparts are compiled and checked**:

- largest-class-first rank-two half weave / Proposition 4.2;
- paper-facing wrappers for Lemmas 5.1 and 6.3;
- shared residual-support proof for Lemma 7.20;
- unrestricted rank-two-flat geometry for Lemmas 8.3–8.5;
- strengthened Lemma 8.8 and revised Proposition 8.11 route;
- structural maximal-family proof of Lemma 9.2 and the six-point matroid bridge.

However, `rankThreeKUM` continues to use the **original compiled rank-two, near-tight, and two-gap routes**. The only major revised route substituted into the exported theorem is the **structural six-point `k = 2` route**. The paper and Appendix A now state this explicitly.

## Principal version-2 declarations

Useful targets include:

- `Rank3KUM.Version2.HalfWeave.CyclicRankTwoBasisOrdering`
- `Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense`
- `Rank3KUM.Version2.isBase_insert_pair_of_indep_flat_rank3`
- `Rank3KUM.Version2.isBase_insert_pair_of_contract_indep_rank3`
- `Rank3KUM.Version2.residualSupport_disjoint_of_shared_bridge`
- `Rank3KUM.Version2.eRk_union_eq_three_of_distinct_rankTwo_flats`
- `Rank3KUM.Version2.eRk_inter_le_one_of_distinct_rankTwo_flats`
- `Rank3KUM.Version2.inter_subset_closure_singleton_of_distinct_rankTwo_flats`
- `Rank3KUM.Version2.nearTight_eq_one_of_nonconcurrent_three`
- `Rank3KUM.Version2.exists_isBase_hitsNearTight_of_strict_rankThree`
- `Rank3KUM.Version2.LinearTripleFamily6`
- `Rank3KUM.Version2.exists_avoidingCycle6_of_linear`
- `Rank3KUM.Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural`
- `Rank3KUM.rankThreeKUM`

## Six-point rewrite

The old six-point proof used a large finite certificate with eight hard-coded orders. Version 2 adds a structural proof:

1. dependent triples form a linear triple family on six points;
2. every point has degree at most two, hence `|F| <= 4` by incidence counting;
3. extend to a maximal linear family;
4. classify maximal families, up to relabeling, as either `{012,345}` or the Pasch family `{012,034,135,245}`;
5. verify the paper's exact avoiding cycles `(0,1,3,2,4,5)` and `(0,1,4,2,3,5)`;
6. translate the avoiding cycle back to a cyclic basis order of the strict six-point matroid.

This structural bridge is the active `k = 2` dependency of `rankThreeKUM`. The old finite certificate remains compiled as a legacy/fallback route and source of shared geometry; it was not deleted.

## Lemma 8.5 correspondence subtlety

The version-2 unrestricted theorem directly checks

`A ∩ B ⊆ cl({e})`

for distinct rank-two flats with `e ∈ A ∩ B`. The paper's general cardinality consequence `|A ∩ B| <= k - 1` under the strict-density hypotheses is then derived from the rank-one/parallel-class bound of Lemma 3.2 (`StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one`). The older near-tight-specific cardinality theorem is **not** being presented as the general correspondence.

## Definition 4.1 correspondence

Appendix A now points Definition 4.1 to

`Rank3KUM.Version2.HalfWeave.CyclicRankTwoBasisOrdering`.

Lean represents the cyclic `2k` positions as `Fin k × Bool`; the structure consists of an equivalence to the ground set plus the adjacent-successor basis property. The construction theorem still obtains canonical input from the legacy sorted enumeration, but after that point its proof requires only “largest class first.”

## Paper artifact alignment

The updated HTML was produced from the attached pre-alignment v2 HTML by the reviewed `tools/update_v2_paper_alignment.py` logic. The artifact pass:

- replaced **76** old immutable `f956680...` source-link occurrences with `0c98e5c...`;
- uniquely replaced **13** Appendix A rows, including the previously overlooked Definition 4.1 row;
- removed the stale statements that the strengthened 8.8 / structural 9.2 route was awaiting formalization;
- changed wording to distinguish compiled alternatives from actual `rankThreeKUM` dependencies;
- corrected Lemma 8.5's general-cardinality correspondence;
- uses a duplicate-sensitive Appendix-row replacement check. CI includes a regression test requiring a duplicated Lemma 5.1 row to be rejected.

The updated PDF was rendered from the updated HTML with WeasyPrint 68.0. It is a 19-page Letter PDF. A render-first visual inspection found no clipped text, overlapping content, black glyph boxes, or Appendix table overflow. References are intentionally forced to a new page by the pre-existing stylesheet, leaving page 16 mostly blank after the acknowledgements continuation; this is inherited layout behavior rather than missing content.

Artifact SHA-256 checksums from this generation pass:

- updated HTML: `26da40f55e4dd83f6d0622771403afad6c1a53cad3b82c4243c6d76a0a3ad242`
- updated PDF: `8f6887a8fa5b069a042799fd04ed4965de34781d1aab57f257ccdb999b53fd00`

## Scope boundaries

- The repository machine-checks the complete **divisible rank-three** theorem (`|E| = 3k`).
- Corollary 1.3 combines it mathematically with the published coprime theorem of van den Heuvel and Thomassé; that external coprime ingredient is not formalized here.
- The version-2 work is largely **additive**, not a repository-size cleanup: roughly 2,500 Lean lines were added while legacy machinery was retained. This is intentional for proof stability.
- The paper credits McGuinness for deletion plus contiguous insertion and the paving rank-three two-gap argument; the present result is phrased as an extension to arbitrary rank-three matroids, without an unqualified priority claim for the local formulation.

## Suggested review questions

Please independently check:

1. whether the paper's revised mathematical proofs are sound, especially Proposition 4.2, Lemma 7.20, Lemma 8.8/Proposition 8.11, and Lemma 9.2;
2. whether the version-2 Lean statements really match those paper claims (including hidden strength/weakness in hypotheses);
3. whether Appendix A accurately distinguishes direct declarations, derived correspondences, checked alternatives, and actual main-theorem dependencies;
4. whether `rankThreeKUM` really uses the structural six-point theorem and does not secretly depend on the legacy eight-order certificate for its `k = 2` callback;
5. whether any paper wording overstates what is formalized, especially Corollary 1.3;
6. whether the new additive formalization introduces any unsound axiom, `sorry`, `unsafe`, `native_decide`, or trust-boundary issue;
7. whether any bibliographic or priority language still needs qualification.

No further broad cleanup is recommended unless review finds a concrete defect.
