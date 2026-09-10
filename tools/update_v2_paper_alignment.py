#!/usr/bin/env python3
"""Apply the post-formalization alignment edits to Rank3KUM_paper_v2_draft.html.

Usage:
    python3 tools/update_v2_paper_alignment.py \
        Rank3KUM_paper_v2_draft.html Rank3KUM_paper_v2_aligned.html

The script is intentionally narrow: it updates formalization-status prose, immutable
GitHub commit links, and the Appendix A rows whose Lean correspondence changed.
It does not rewrite the mathematical proofs or bibliography.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

OLD_FULL = "f956680a3ed2ce7215e438c0e7d97815f6c2fd2b"
OLD_SHORT = "f956680"
NEW_FULL = "0c98e5cd9341a65f309e0d5d55907b8656c70e62"
NEW_SHORT = "0c98e5c"
BASE = f"https://github.com/afletcher22/Rank3KUM/blob/{NEW_FULL}/"
TREE = f"https://github.com/afletcher22/Rank3KUM/tree/{NEW_FULL}"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def replace_row(text: str, label_pattern: str, new_row: str) -> str:
    pattern = rf"<tr><td>{label_pattern}</td>.*?</tr>"
    out, count = re.subn(pattern, new_row, text, count=1, flags=re.DOTALL)
    if count != 1:
        raise RuntimeError(f"Appendix row {label_pattern!r}: expected one match, found {count}")
    return out


def link(path: str, name: str) -> str:
    return f'<a href="{BASE}{path}">{name}</a>'


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: update_v2_paper_alignment.py INPUT.html OUTPUT.html")
    src = Path(sys.argv[1])
    dst = Path(sys.argv[2])
    text = src.read_text(encoding="utf-8")

    # Move all old immutable source links to the checked v2 code commit. Old
    # declarations remain present there; changed correspondences are rewritten below.
    text = text.replace(OLD_FULL, NEW_FULL)

    old = (
        '<p>The divisible theorem (Theorem 1.2) is proved in the existing Lean 4 development. '
        'Corollary 1.3 also uses the external coprime-case theorem, which is not formalized here. '
        'This draft simplifies the rank-two construction, strengthens Lemma 8.8, and replaces the '
        'finite-certificate exposition in §9 by a structural proof. Those revised arguments have not '
        'yet been incorporated into Lean. Appendix A distinguishes existing formal results from the '
        'remaining alignment work.</p>'
    )
    new = (
        '<p>The divisible theorem (Theorem 1.2) and the revised proof route used in this version are '
        'now checked in Lean 4. Corollary 1.3 still also uses the external coprime-case theorem of van '
        'den Heuvel and Thomassé, which is not formalized here. In particular, the largest-class-first '
        'rank-two construction, the strengthened Lemma 8.8 and revised Proposition 8.11 route, and the '
        'structural six-point proof of Lemma 9.2 have all been incorporated into the version-2 '
        'development. Appendix A records the checked correspondences.</p>'
    )
    text = replace_once(text, old, new, "front formalization status")

    old = (
        f'<p>The comparison uses <a href="{TREE}">Rank3KUM, commit {OLD_SHORT}</a>, whose Lean source '
        'is unchanged from the commit cited in version 1. The tag <code>v1.0.0</code> points to '
        '<code>fa57894</code>; the two subsequent commits leading to <code>f956680</code> change only '
        'the README. All Lean files agree across <code>90e661d</code>, <code>fa57894</code>, and '
        f'<code>f956680</code>. The archived formalization is <a href="https://doi.org/10.5281/zenodo.21813155">'
        '10.5281/zenodo.21813155</a>.</p>'
    )
    # Because the global hash replacement already changed the URL, match the text-only old paragraph
    # separately if needed.
    if old not in text:
        pattern = (
            r'<p>The comparison uses <a href="https://github\.com/afletcher22/Rank3KUM/tree/'
            + re.escape(NEW_FULL)
            + r'">Rank3KUM, commit f956680</a>.*?10\.5281/zenodo\.21813155</a>\.</p>'
        )
        # Normalize accidental double escaping in this fallback pattern before use.
        pattern = pattern.replace(r'\\.', r'\.')
        repl = (
            f'<p>The version-2 correspondence below is checked against '
            f'<a href="{TREE}">Rank3KUM, commit {NEW_SHORT}</a>. CI run '
            '<code>34520738803</code> completed successfully with <code>3058</code> build jobs. '
            'The principal theorem and the new structural six-point theorems have exactly the axiom '
            'dependencies <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. '
            'The archived version-1 formalization remains '
            '<a href="https://doi.org/10.5281/zenodo.21813155">10.5281/zenodo.21813155</a>; it should '
            'not be confused with this checked version-2 branch state.</p>'
        )
        text, count = re.subn(pattern, repl, text, count=1, flags=re.DOTALL)
        if count != 1:
            raise RuntimeError(f"comparison paragraph: expected one match, found {count}")
    else:
        text = replace_once(
            text,
            old,
            f'<p>The version-2 correspondence below is checked against <a href="{TREE}">Rank3KUM, '
            f'commit {NEW_SHORT}</a>. CI run <code>34520738803</code> completed successfully with '
            '<code>3058</code> build jobs. The principal theorem and the new structural six-point '
            'theorems have exactly the axiom dependencies <code>propext</code>, '
            '<code>Classical.choice</code> and <code>Quot.sound</code>. The archived version-1 '
            'formalization remains <a href="https://doi.org/10.5281/zenodo.21813155">'
            '10.5281/zenodo.21813155</a>; it should not be confused with this checked version-2 '
            'branch state.</p>',
            "comparison paragraph",
        )

    text = replace_once(
        text,
        '<p>In particular, a set containing representatives of A∩B, A∩C and B∩C meets every near-tight '
        'flat. This is the weaker avoidance conclusion established by the existing Lean development; the '
        'stronger classification above awaits formalization.</p>',
        '<p>In particular, a set containing representatives of A∩B, A∩C and B∩C meets every near-tight '
        'flat. The stronger no-fourth-flat statement above is formalized in the version-2 development as '
        '<code>Rank3KUM.Version2.nearTight_eq_one_of_nonconcurrent_three</code>; the earlier avoidance '
        'theorem is retained as a compatible weaker result.</p>',
        "Lemma 8.8 note",
    )

    text = replace_once(
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

    old11 = (
        '<p>The existing development uses Lean 4.33.0-rc2 and the Mathlib revision pinned in its manifest. '
        'At the reviewed commit, the project has approximately 10,000 lines across 37 Lean files, including '
        'the root import file. The successful CI build reports 3,046 jobs. The principal theorem has precisely '
        'the axiom dependencies <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>; '
        'no mathematical hypothesis is introduced as a custom axiom.</p>'
    )
    new11 = (
        '<p>The version-2 development uses Lean 4.33.0-rc2 and the Mathlib revision pinned in its manifest. '
        f'At the checked commit <code>{NEW_SHORT}</code>, the successful root CI build reports 3,058 jobs. '
        'The principal theorem has precisely the axiom dependencies <code>propext</code>, '
        '<code>Classical.choice</code> and <code>Quot.sound</code>; the two new structural six-point endpoint '
        'theorems print the same dependencies. No mathematical hypothesis is introduced as a custom axiom.</p>'
    )
    text = replace_once(text, old11, new11, "Section 11 first paragraph")

    old11b = (
        '<p>The development contains no <code>sorry</code>, <code>admit</code>, custom <code>axiom</code> or '
        '<code>unsafe</code> declarations, and uses no <code>native_decide</code>. The six-point certificate is '
        'proved by a propositional decision tree; small finite equalities are discharged by kernel evaluation '
        'with <code>decide</code>.</p>'
    )
    new11b = (
        '<p>The development contains no <code>sorry</code>, <code>admit</code>, custom <code>axiom</code> or '
        '<code>unsafe</code> declarations, and uses no <code>native_decide</code>. The active six-point proof is '
        'structural: dependent triples form a linear family, maximal linear families are classified as the '
        'two-disjoint-triple or Pasch configuration, and the two explicit cycles in Lemma 9.2 are checked '
        'window by window. Small closed finite equalities may still be discharged by kernel evaluation with '
        '<code>decide</code>. The older propositional finite certificate remains compiled but is not the active '
        'base-case route.</p>'
    )
    text = replace_once(text, old11b, new11b, "Section 11 second paragraph")

    old11c = (
        '<p>Three distinctions matter when comparing this revision with the code. First, the rank-two structure '
        'packages the block-order construction, whereas Definition 4.1 describes the resulting cyclic ordering. '
        'Second, the code proves the avoidance consequence of Lemma 8.8, not its stronger classification. Third, '
        'the code retains the finite certificate for §9 rather than the maximal-family proof. These differences do '
        'not change the statement of the already formalized main theorem, but the revised proof route has not yet '
        'been checked in Lean. Appendix A records the outstanding correspondences.</p>'
    )
    new11c = (
        '<p>The principal expository distinctions in this revision are now represented explicitly in the '
        '<code>Rank3KUM.Version2</code> modules. The largest-class-first half-weave has its own checked output '
        'theorem; the stronger Lemma 8.8 and the revised hitting-basis route are checked; and §9 has a checked '
        'maximal-family classification and matroid bridge. The original declarations are retained where useful '
        'for compatibility, so Appendix A distinguishes the version-2 counterparts from legacy routes rather '
        'than treating them as outstanding work.</p>'
    )
    text = replace_once(text, old11c, new11c, "Section 11 third paragraph")

    old_ack = (
        '<p>Under the direction of Austen Fletcher, the original mathematical argument was developed primarily '
        'by GPT-5.6 Sol. The original Lean formalization and paper were prepared collaboratively by GPT-5.6 Sol '
        'and Claude Opus 5. This revision incorporates AI-assisted critical review and expository simplification. '
        'The existing divisible theorem and its formal dependencies were checked by the Lean kernel. The new proof '
        'presentations and stronger near-tight statement are distinguished from that checked development in §11 '
        'and Appendix A.</p>'
    )
    new_ack = (
        '<p>Under the direction of Austen Fletcher, the original mathematical argument was developed primarily '
        'by GPT-5.6 Sol. The original Lean formalization and paper were prepared collaboratively by GPT-5.6 Sol '
        'and Claude Opus 5. This revision incorporates AI-assisted critical review and expository simplification, '
        'and its revised Lean correspondences were subsequently implemented and checked. The divisible theorem, '
        'including the version-2 rank-two, near-tight and structural six-point routes described in Appendix A, '
        'was checked by the Lean kernel at the commit stated there.</p>'
    )
    text = replace_once(text, old_ack, new_ack, "acknowledgements")

    # Appendix introduction.
    pattern = (
        r'<p>The table refers to <a href="https://github\.com/afletcher22/Rank3KUM/tree/'
        + re.escape(NEW_FULL)
        + r'">commit f956680</a>\. Links identify immutable source locations\. A compiled result may use a '
          r'different representation or proof; the status column records substantive differences\. In particular, '
          r'the revised arguments for Proposition 4\.2 and Lemmas 8\.8 and 9\.2 remain to be aligned with Lean\.</p>'
    )
    pattern = pattern.replace(r'\\.', r'\.')
    repl = (
        f'<p>The table refers to <a href="{TREE}">checked commit {NEW_SHORT}</a>. Links identify immutable '
        'source locations. A compiled result may use a different representation or proof; the status column '
        'records substantive differences and notes when a version-2 declaration supersedes a legacy proof route. '
        'The revised arguments for Proposition 4.2, Lemma 8.8, Proposition 8.11 and Lemma 9.2 are checked at this '
        'commit.</p>'
    )
    text, count = re.subn(pattern, repl, text, count=1, flags=re.DOTALL)
    if count != 1:
        raise RuntimeError(f"Appendix introduction: expected one match, found {count}")

    text = replace_row(
        text,
        r"Prop\. 4\.2".replace(r"\\.", r"\."),
        '<tr><td>Prop. 4.2</td><td>'
        + link('Rank3KUM/Version2/HalfWeave.lean', 'Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense')
        + '<br/>' + link('Rank3KUM/HalfWeave/ParallelClasses.lean', 'HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense')
        + '</td><td>The version-2 declaration checks the paper\'s largest-class-first construction; the older fully sorted construction remains compiled.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 5\.1".replace(r"\\.", r"\."),
        '<tr><td>Lem. 5.1</td><td>'
        + link('Rank3KUM/Version2/CorrespondenceWrappers.lean', 'Version2.isBase_insert_pair_of_indep_flat_rank3')
        + '<br/>' + link('Rank3KUM/Interleave.lean', 'isBase_insert_pair_of_isBasis_flat_rank3')
        + '</td><td>Version-2 wrapper matches the paper\'s independent-pair hypothesis directly; the original basis-of-flat lemma remains the underlying result.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 6\.3".replace(r"\\.", r"\."),
        '<tr><td>Lem. 6.3</td><td>'
        + link('Rank3KUM/Version2/CorrespondenceWrappers.lean', 'Version2.isBase_insert_pair_of_contract_indep_rank3')
        + '<br/>' + link('Rank3KUM/ContractInterleave.lean', 'isBase_insert_pair_of_contract_isBase_rank3')
        + '</td><td>Version-2 wrapper records the revised independent-pair formulation; the contraction and singleton-basis infrastructure remains in the original module.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 7\.20".replace(r"\\.", r"\."),
        '<tr><td>Lem. 7.20</td><td>'
        + link('Rank3KUM/Version2/ResidualSupportDisjoint.lean', 'Version2 residual-support disjointness lemma')
        + '<br/>' + link('Rank3KUM/TwoGap/EqualDisjointAC.lean', 'legacy specialized disjointness declarations')
        + '</td><td>The version-2 module extracts the paper\'s shared residual-support argument; the three original specialized consequences remain compiled.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 8\.3".replace(r"\\.", r"\."),
        '<tr><td>Lem. 8.3</td><td>'
        + link('Rank3KUM/Version2/NearTightGeometry.lean', 'Version2.eRk_union_eq_three_of_distinct_rankTwo_flats')
        + '</td><td>Version-2 declaration matches the unrestricted distinct-rank-two-flat statement; the old equal-cardinality specialization remains compiled.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 8\.4".replace(r"\\.", r"\."),
        '<tr><td>Lem. 8.4</td><td>'
        + link('Rank3KUM/Version2/NearTightGeometry.lean', 'Version2.eRk_inter_le_one_of_distinct_rankTwo_flats')
        + '</td><td>Version-2 declaration matches the unrestricted paper statement.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 8\.5".replace(r"\\.", r"\."),
        '<tr><td>Lem. 8.5</td><td>'
        + link('Rank3KUM/Version2/NearTightGeometry.lean', 'Version2.inter_subset_closure_singleton_of_distinct_rankTwo_flats')
        + '<br/>' + link('Rank3KUM/NearTightGeometry.lean', 'ncard_inter_le_k_sub_one_of_distinct_nearTight')
        + '</td><td>The unrestricted closure statement is checked in the version-2 module; the existing near-tight cardinality bound supplies the strict-density specialization.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 8\.8".replace(r"\\.", r"\."),
        '<tr><td>Lem. 8.8</td><td>'
        + link('Rank3KUM/Version2/NearTightClassification.lean', 'Version2.nearTight_eq_one_of_nonconcurrent_three')
        + '<br/>' + link('Rank3KUM/NearTightGeometry.lean', 'false_of_nearTight_avoids_three_pairwise_representatives')
        + '</td><td>The stronger no-fourth-flat classification is now compiled and follows the revised incidence-count proof. The older avoidance consequence remains compiled separately.</td></tr>'
    )

    text = replace_row(
        text,
        r"Prop\. 8\.11".replace(r"\\.", r"\."),
        '<tr><td>Prop. 8.11</td><td>'
        + link('Rank3KUM/Version2/NearTightHitting.lean', 'Version2.exists_isBase_hitsNearTight_of_strict_rankThree')
        + '<br/>' + link('Rank3KUM/NearTightGeometry.lean', 'exists_isBase_hitsNearTight_of_strict_rankThree')
        + '</td><td>The version-2 declaration checks the paper\'s route through the stronger Lemma 8.8; the original theorem with the same conclusion remains compiled.</td></tr>'
    )

    text = replace_row(
        text,
        r"Def\. 9\.1".replace(r"\\.", r"\."),
        '<tr><td>Def. 9.1</td><td>'
        + link('Rank3KUM/Version2/SixPointStructural.lean', 'Version2.LinearTripleFamily6')
        + '</td><td>Now packaged directly as the paper\'s named definition of a linear family of triples.</td></tr>'
    )

    text = replace_row(
        text,
        r"Lem\. 9\.2".replace(r"\\.", r"\."),
        '<tr><td>Lem. 9.2</td><td>'
        + link('Rank3KUM/Version2/SixPointLemma9.lean', 'Version2.exists_avoidingCycle6_of_linear')
        + '<br/>' + link('Rank3KUM/Version2/SixPointMaximal.lean', 'maximal linear-family classification')
        + '<br/>' + link('Rank3KUM/Version2/SixPointPasch.lean', 'Pasch relabelling')
        + '</td><td>The structural maximal-family proof is compiled, including the two canonical families and the paper\'s exact avoiding cycles. The old eight-order certificate remains compiled as a legacy route.</td></tr>'
    )

    text = replace_row(
        text,
        r"§9, k = 2",
        '<tr><td>§9, k = 2</td><td>'
        + link('Rank3KUM/Version2/SixPointMatroidBridge.lean', 'Version2.exists_cyclicBasisOrder3_of_ground_encard_six_structural')
        + '<br/>' + link('Rank3KUM/FinalInduction.lean', 'rankThreeKUM')
        + '</td><td>The structural Section 9 theorem is compiled and is now the active k = 2 callback used by the exported main theorem.</td></tr>'
    )

    dst.write_text(text, encoding="utf-8")
    print(f"wrote {dst}")


if __name__ == "__main__":
    main()
