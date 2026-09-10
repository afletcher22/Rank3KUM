#!/usr/bin/env python3
"""Align the v2 Rank3KUM paper with the checked version-2 Lean development.

Usage:
    python3 tools/update_v2_paper_alignment.py INPUT.html [OUTPUT.html]

With no OUTPUT path the script performs the full validation pass without writing a file.
With OUTPUT it writes the aligned HTML. The mathematical body and bibliography are left
untouched; only formalization-status prose, immutable source links, and affected Appendix A
rows are changed.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

OLD_FULL = "f956680a3ed2ce7215e438c0e7d97815f6c2fd2b"
NEW_FULL = "0c98e5cd9341a65f309e0d5d55907b8656c70e62"
NEW_SHORT = "0c98e5c"
TREE = f"https://github.com/afletcher22/Rank3KUM/tree/{NEW_FULL}"
BASE = f"https://github.com/afletcher22/Rank3KUM/blob/{NEW_FULL}/"
CI_RUN = "34520738803"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def replace_row(text: str, label: str, correspondence: str, status: str) -> str:
    pattern = rf"<tr><td>{re.escape(label)}</td>.*?</tr>"
    row = f"<tr><td>{label}</td><td>{correspondence}</td><td>{status}</td></tr>"
    out, count = re.subn(pattern, row, text, count=1, flags=re.DOTALL)
    if count != 1:
        raise RuntimeError(f"Appendix row {label!r}: expected exactly one match, found {count}")
    return out


def link(path: str, name: str) -> str:
    return f'<a href="{BASE}{path}">{name}</a>'


def align(text: str) -> str:
    old_link_count = text.count(OLD_FULL)
    if old_link_count == 0:
        raise RuntimeError("expected at least one immutable f956680 source link")
    text = text.replace(OLD_FULL, NEW_FULL)

    text = replace_exact(
        text,
        '<p>The divisible theorem (Theorem 1.2) is proved in the existing Lean 4 development. '
        'Corollary 1.3 also uses the external coprime-case theorem, which is not formalized here. '
        'This draft simplifies the rank-two construction, strengthens Lemma 8.8, and replaces the '
        'finite-certificate exposition in §9 by a structural proof. Those revised arguments have not '
        'yet been incorporated into Lean. Appendix A distinguishes existing formal results from the '
        'remaining alignment work.</p>',
        '<p>The divisible theorem (Theorem 1.2) and the revised proof route used in this version are now '
        'checked in Lean 4. Corollary 1.3 still also uses the external coprime-case theorem of van den '
        'Heuvel and Thomassé, which is not formalized here. In particular, the largest-class-first '
        'rank-two construction, the strengthened Lemma 8.8 and revised Proposition 8.11 route, and the '
        'structural six-point proof of Lemma 9.2 have all been incorporated into the version-2 '
        'development. Appendix A records the checked correspondences.</p>',
        "front formalization status",
    )

    text = replace_exact(
        text,
        f'<p>The comparison uses <a href="{TREE}">Rank3KUM, commit f956680</a>, whose Lean source is '
        'unchanged from the commit cited in version 1. The tag <code>v1.0.0</code> points to '
        '<code>fa57894</code>; the two subsequent commits leading to <code>f956680</code> change only '
        'the README. All Lean files agree across <code>90e661d</code>, <code>fa57894</code>, and '
        '<code>f956680</code>. The archived formalization is '
        '<a href="https://doi.org/10.5281/zenodo.21813155">10.5281/zenodo.21813155</a>.</p>',
        f'<p>The version-2 correspondence below is checked against <a href="{TREE}">Rank3KUM, commit '
        f'{NEW_SHORT}</a>. CI run <code>{CI_RUN}</code> completed successfully with <code>3058</code> '
        'build jobs. The principal theorem and the new structural six-point theorems have exactly the '
        'axiom dependencies <code>propext</code>, <code>Classical.choice</code> and '
        '<code>Quot.sound</code>. The archived version-1 formalization remains '
        '<a href="https://doi.org/10.5281/zenodo.21813155">10.5281/zenodo.21813155</a>; it should not '
        'be confused with this checked version-2 branch state.</p>',
        "comparison paragraph",
    )

    text = replace_exact(
        text,
        '<p>In particular, a set containing representatives of A∩B, A∩C and B∩C meets every near-tight '
        'flat. This is the weaker avoidance conclusion established by the existing Lean development; the '
        'stronger classification above awaits formalization.</p>',
        '<p>In particular, a set containing representatives of A∩B, A∩C and B∩C meets every near-tight '
        'flat. The stronger no-fourth-flat statement above is formalized in the version-2 development as '
        '<code>Rank3KUM.Version2.nearTight_eq_one_of_nonconcurrent_three</code>; the earlier avoidance '
        'theorem is retained as a compatible weaker result.</p>',
        "Lemma 8.8 status note",
    )

    text = replace_exact(
        text,
        '<p>The existing formalization proves the required avoidance result through an eight-order finite '
        'certificate. The structural proof above replaces that exposition; its maximal-family classification '
        'has not yet been formalized.</p>',
        '<p>The structural proof above is now formalized. The checked development defines linear triple '
        'families, extends them to maximal families, proves the pair/Pasch classification, verifies the two '
        'displayed avoiding cycles, and translates the resulting cycle back to the strict six-element matroid '
        'case. The original eight-order finite certificate remains compiled as a legacy route but is no longer '
        'the <code>k = 2</code> route used by <code>rankThreeKUM</code>.</p>',
        "Section 9 closing status",
    )

    text = replace_exact(
        text,
        '<p>The existing development uses Lean 4.33.0-rc2 and the Mathlib revision pinned in its manifest. '
        'At the reviewed commit, the project has approximately 10,000 lines across 37 Lean files, including '
        'the root import file. The successful CI build reports 3,046 jobs. The principal theorem has precisely '
        'the axiom dependencies <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>; '
        'no mathematical hypothesis is introduced as a custom axiom.</p>',
        f'<p>The version-2 development uses Lean 4.33.0-rc2 and the Mathlib revision pinned in its manifest. '
        f'At the checked commit <code>{NEW_SHORT}</code>, the successful root CI build reports 3,058 jobs. '
        'The principal theorem has precisely the axiom dependencies <code>propext</code>, '
        '<code>Classical.choice</code> and <code>Quot.sound</code>; the two new structural six-point endpoint '
        'theorems print the same dependencies. No mathematical hypothesis is introduced as a custom axiom.</p>',
        "Section 11 build/axiom paragraph",
    )

    text = replace_exact(
        text,
        '<p>The development contains no <code>sorry</code>, <code>admit</code>, custom <code>axiom</code> or '
        '<code>unsafe</code> declarations, and uses no <code>native_decide</code>. The six-point certificate is '
        'proved by a propositional decision tree; small finite equalities are discharged by kernel evaluation '
        'with <code>decide</code>.</p>',
        '<p>The development contains no <code>sorry</code>, <code>admit</code>, custom <code>axiom</code> or '
        '<code>unsafe</code> declarations, and uses no <code>native_decide</code>. The active six-point proof is '
        'structural: dependent triples form a linear family, maximal linear families are classified as the '
        'two-disjoint-triple or Pasch configuration, and the two explicit cycles in Lemma 9.2 are checked '
        'window by window. Small closed finite equalities may still be discharged by kernel evaluation with '
        '<code>decide</code>. The older propositional finite certificate remains compiled but is not the active '
        'base-case route.</p>',
        "Section 11 decision-procedure paragraph",
    )

    text = replace_exact(
        text,
        '<p>Three distinctions matter when comparing this revision with the code. First, the rank-two structure '
        'packages the block-order construction, whereas Definition 4.1 describes the resulting cyclic ordering. '
        'Second, the code proves the avoidance consequence of Lemma 8.8, not its stronger classification. Third, '
        'the code retains the finite certificate for §9 rather than the maximal-family proof. These differences do '
        'not change the statement of the already formalized main theorem, but the revised proof route has not yet '
        'been checked in Lean. Appendix A records the outstanding correspondences.</p>',
        '<p>The principal expository distinctions in this revision are now represented explicitly in the '
        '<code>Rank3KUM.Version2</code> modules. The largest-class-first half-weave has its own checked output '
        'theorem; the stronger Lemma 8.8 and the revised hitting-basis route are checked; and §9 has a checked '
        'maximal-family classification and matroid bridge. The original declarations are retained where useful '
        'for compatibility, so Appendix A distinguishes the version-2 counterparts from legacy routes rather '
        'than treating them as outstanding work.</p>',
        "Section 11 correspondence paragraph",
    )

    text = replace_exact(
        text,
        '<p>Under the direction of Austen Fletcher, the original mathematical argument was developed primarily '
        'by GPT-5.6 Sol. The original Lean formalization and paper were prepared collaboratively by GPT-5.6 Sol '
        'and Claude Opus 5. This revision incorporates AI-assisted critical review and expository simplification. '
        'The existing divisible theorem and its formal dependencies were checked by the Lean kernel. The new proof '
        'presentations and stronger near-tight statement are distinguished from that checked development in §11 '
        'and Appendix A.</p>',
        '<p>Under the direction of Austen Fletcher, the original mathematical argument was developed primarily '
        'by GPT-5.6 Sol. The original Lean formalization and paper were prepared collaboratively by GPT-5.6 Sol '
        'and Claude Opus 5. This revision incorporates AI-assisted critical review and expository simplification, '
        'and its revised Lean correspondences were subsequently implemented and checked. The divisible theorem, '
        'including the version-2 rank-two, near-tight and structural six-point routes described in Appendix A, '
        'was checked by the Lean kernel at the commit stated there.</p>',
        "acknowledgements",
    )

    text = replace_exact(
        text,
        f'<p>The table refers to <a href="{TREE}">commit f956680</a>. Links identify immutable source '
        'locations. A compiled result may use a different representation or proof; the status column records '
        'substantive differences. In particular, the revised arguments for Proposition 4.2 and Lemmas 8.8 and '
        '9.2 remain to be aligned with Lean.</p>',
        f'<p>The table refers to <a href="{TREE}">checked commit {NEW_SHORT}</a>. Links identify immutable '
        'source locations. A compiled result may use a different representation or proof; the status column '
        'records substantive differences and notes when a version-2 declaration supersedes a legacy proof route. '
        'The revised arguments for Proposition 4.2, Lemma 8.8, Proposition 8.11 and Lemma 9.2 are checked at this '
        'commit.</p>',
        "Appendix introduction",
    )

    rows = {
        "Prop. 4.2": (
            link('Rank3KUM/Version2/HalfWeave.lean', 'Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense')
            + '<br/>' + link('Rank3KUM/HalfWeave/ParallelClasses.lean', 'HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense'),
            "The version-2 declaration checks the paper's largest-class-first construction; the older fully sorted construction remains compiled.",
        ),
        "Lem. 5.1": (
            link('Rank3KUM/Version2/CorrespondenceWrappers.lean', 'Version2.isBase_insert_pair_of_indep_flat_rank3')
            + '<br/>' + link('Rank3KUM/Interleave.lean', 'isBase_insert_pair_of_isBasis_flat_rank3'),
            "Version-2 wrapper matches the paper's independent-pair hypothesis directly; the original basis-of-flat lemma remains the underlying result.",
        ),
        "Lem. 6.3": (
            link('Rank3KUM/Version2/CorrespondenceWrappers.lean', 'Version2.isBase_insert_pair_of_contract_indep_rank3')
            + '<br/>' + link('Rank3KUM/ContractInterleave.lean', 'isBase_insert_pair_of_contract_isBase_rank3'),
            "Version-2 wrapper records the revised independent-pair formulation; the contraction and singleton-basis infrastructure remains in the original module.",
        ),
        "Lem. 7.20": (
            link('Rank3KUM/Version2/ResidualSupportDisjoint.lean', 'Version2 residual-support disjointness lemma')
            + '<br/>' + link('Rank3KUM/TwoGap/EqualDisjointAC.lean', 'legacy specialized disjointness declarations'),
            "The version-2 module extracts the paper's shared residual-support argument; the three original specialized consequences remain compiled.",
        ),
        "Lem. 8.3": (
            link('Rank3KUM/Version2/NearTightGeometry.lean', 'Version2.eRk_union_eq_three_of_distinct_rankTwo_flats'),
            "Version-2 declaration matches the unrestricted distinct-rank-two-flat statement; the old equal-cardinality specialization remains compiled.",
        ),
        "Lem. 8.4": (
            link('Rank3KUM/Version2/NearTightGeometry.lean', 'Version2.eRk_inter_le_one_of_distinct_rankTwo_flats'),
            "Version-2 declaration matches the unrestricted paper statement.",
        ),
        "Lem. 8.5": (
            link('Rank3KUM/Version2/NearTightGeometry.lean', 'Version2.inter_subset_closure_singleton_of_distinct_rankTwo_flats')
            + '<br/>' + link('Rank3KUM/NearTightGeometry.lean', 'ncard_inter_le_k_sub_one_of_distinct_nearTight'),
            "The unrestricted closure statement is checked in the version-2 module; the existing near-tight cardinality bound supplies the strict-density specialization.",
        ),
        "Lem. 8.8": (
            link('Rank3KUM/Version2/NearTightClassification.lean', 'Version2.nearTight_eq_one_of_nonconcurrent_three')
            + '<br/>' + link('Rank3KUM/NearTightGeometry.lean', 'false_of_nearTight_avoids_three_pairwise_representatives'),
            "The stronger no-fourth-flat classification is now compiled and follows the revised incidence-count proof. The older avoidance consequence remains compiled separately.",
        ),
        "Prop. 8.11": (
            link('Rank3KUM/Version2/NearTightHitting.lean', 'Version2.exists_isBase_hitsNearTight_of_strict_rankThree')
            + '<br/>' + link('Rank3KUM/NearTightGeometry.lean', 'exists_isBase_hitsNearTight_of_strict_rankThree'),
            "The version-2 declaration checks the paper's route through the stronger Lemma 8.8; the original theorem with the same conclusion remains compiled.",
        ),
        "Def. 9.1": (
            link('Rank3KUM/Version2/SixPointStructural.lean', 'Version2.LinearTripleFamily6'),
            "Now packaged directly as the paper's named definition of a linear family of triples.",
        ),
        "Lem. 9.2": (
            link('Rank3KUM/Version2/SixPointLemma9.lean', 'Version2.exists_avoidingCycle6_of_linear')
            + '<br/>' + link('Rank3KUM/Version2/SixPointMaximal.lean', 'maximal linear-family classification')
            + '<br/>' + link('Rank3KUM/Version2/SixPointPasch.lean', 'Pasch relabelling'),
            "The structural maximal-family proof is compiled, including the two canonical families and the paper's exact avoiding cycles. The old eight-order certificate remains compiled as a legacy route.",
        ),
        "§9, k = 2": (
            link('Rank3KUM/Version2/SixPointMatroidBridge.lean', 'Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural')
            + '<br/>' + link('Rank3KUM/FinalInduction.lean', 'rankThreeKUM'),
            "The structural Section 9 theorem is compiled and is now the active k = 2 callback used by the exported main theorem.",
        ),
    }
    for label, (correspondence, status) in rows.items():
        text = replace_row(text, label, correspondence, status)

    stale = [
        "Those revised arguments have not yet been incorporated into Lean",
        "stronger classification above awaits formalization",
        "maximal-family classification has not yet been formalized",
        "the revised proof route has not yet been checked in Lean",
        "remain to be aligned with Lean",
    ]
    found = [phrase for phrase in stale if phrase in text]
    if found:
        raise RuntimeError(f"stale formalization-status prose remains: {found}")
    if OLD_FULL in text:
        raise RuntimeError("old f956680 immutable source link remains after alignment")

    print(f"validated {old_link_count} immutable source-link updates and {len(rows)} Appendix row replacements")
    return text


def main() -> None:
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: update_v2_paper_alignment.py INPUT.html [OUTPUT.html]")
    src = Path(sys.argv[1])
    aligned = align(src.read_text(encoding="utf-8"))
    if len(sys.argv) == 3:
        dst = Path(sys.argv[2])
        dst.write_text(aligned, encoding="utf-8")
        print(f"wrote {dst}")
    else:
        print("validation only; no output file written")


if __name__ == "__main__":
    main()
