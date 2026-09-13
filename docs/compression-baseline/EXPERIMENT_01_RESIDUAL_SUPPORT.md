# Experiment 01 — shared residual-support argument

## Question

Can the three active equal-singleton residual-support disjointness proofs in the two-gap route be
factored through the single shared argument corresponding to paper v2 Lemma 7.20 **without changing
the advertised theorem**, and does doing so simplify the active dependency structure rather than
merely shorten source text?

## Baseline

Mechanical baseline artifact:

- workflow run `34727057501`
- artifact `10307664773`
- digest `sha256:c1bdc2fcd2b8a77739b35b8999ea3f65922879db00a66e56abb09c6124b52b1e`
- parent Palomar-compatible mathematical baseline `abced491e10f618400e1c9739d2d9503477da76f`

The baseline active route contained three independently proved specializations:

- `TwoGap.equal_singleton_residualSupport_a_disjoint_c`
- `TwoGap.equal_singleton_residualSupport_a_disjoint_b`
- `TwoGap.equal_singleton_residualSupport_b_disjoint_c`

A generic version-2 theorem with the common proof was compiled, but was outside the transitive
closure of `Rank3KUM.rankThreeKUM`.

## Change

A neutral module, `Rank3KUM/TwoGap/ResidualSupportDisjoint.lean`, now contains the common theorem

`Rank3KUM.TwoGap.residualSupport_disjoint_of_shared_bridge`.

The three old specialization names remain available, but their proofs are thin instantiations of the
shared theorem. The paper-facing declaration
`Rank3KUM.Version2.residualSupport_disjoint_of_shared_bridge` is also retained as a thin wrapper, so
the paper correspondence is preserved while the shared argument is now on the active proof route.

This arrangement avoids the import cycle that would result from trying to import the previous
version-2 module backwards into the legacy two-gap files.

## Verification

Experimental head checked by workflow:

- commit `041f158dde4fedb41723b9afb020aa26863a2a0d`
- workflow run `34727512574`
- mechanical-map job: **success**
- Palomar-pinned Comparator + NanoDa drift guard: **success**
- frozen `Challenge.lean` diff against `palomar`: **clean**
- direct `Challenge.lean` check: **success**
- direct `Solution.lean` check: **success**
- full `lake build`: **success**

New map artifact:

- artifact `10309045034`
- digest `sha256:04040345f1ad9415875d9de68b9a917fcf5198323f696c32d4be8ce604e8ea68`

Thus this experiment changes proof structure underneath the same Palomar statement surface. No
statement-contract field changed.

## Mechanical before/after

| Metric | Baseline | Experiment 01 | Delta |
|---|---:|---:|---:|
| Loaded `Rank3KUM.*` declarations | 901 | 898 | -3 |
| Active declarations in `rankThreeKUM` closure | 647 | 646 | -1 |
| Active project-local declaration edges | 1538 | 1526 | **-12** |
| Active modules | 40 | 41 | +1 |
| Maximum shortest root depth | 12 | 12 | 0 |
| Nontrivial SCCs | 0 | 0 | 0 |
| Active theorem declarations | 575 | 574 | -1 |

The extra active module is the new neutral shared-argument module. The active graph nevertheless has
fewer declarations and twelve fewer project-local edges.

The same one-declaration reduction propagates through the relevant nested closures:

| Endpoint | Baseline closure | Experiment 01 closure | Delta |
|---|---:|---:|---:|
| `TwoGap.false_of_equal_singleton_partner_pairs` | 65 | 64 | -1 |
| `TwoGap.universalTwoGapInsertion` | 133 | 132 | -1 |
| `exists_cyclicBasisOrder3_of_cyclic_basis_deletion` | 218 | 217 | -1 |
| `rankThreeKUM` | 647 | 646 | -1 |

The modest declaration-count change understates the factorization because Lean creates internal
helper declarations for tactic-generated set-normalization proofs. At the named-theorem level the
three specialization nodes become much thinner:

- `a_disjoint_c`: 17 direct project dependencies -> 6;
- `a_disjoint_b`: 16 -> 6;
- `b_disjoint_c`: 14 -> 6.

All three now depend on the same active shared theorem. The version-2 paper-facing wrapper changes
from a full duplicate proof with 17 direct project dependencies to a thin wrapper with 4.

## Interpretation

This counts as **small but genuine structural compression** under the project criterion. It is not
just syntactic shortening: the active theorem graph now contains one common mathematical argument
where it previously contained three copies, and the active graph loses twelve edges overall.

It is deliberately not claimed to be a dramatic reduction. The three specialization declarations
are still active because `EqualContradiction.lean` calls them. A follow-up ablation can test whether
calling the generic theorem directly from the contradiction proof removes those wrapper nodes from
the active closure without making the parent proof less readable. That should be judged by a fresh
mechanical map rather than assumed in advance.

## Informal/formal alignment note

The historical v2 alignment manifest correctly records the published v2 baseline, where the shared
Lemma 7.20 theorem was additive and the specialized results remained active. This experimental
branch intentionally changes that proof-route fact: the shared Lemma 7.20 argument is now active.
The mathematical statement corresponding to paper Theorem 1.2 is unchanged.

If this architecture survives into the eventual release, the next paper version should update only
its proof/formalization correspondence language; the theorem statement itself should not change.
