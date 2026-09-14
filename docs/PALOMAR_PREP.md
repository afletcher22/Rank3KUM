# Palomar Registry preparation for Rank3KUM version 3

`version-3` is the publication and Palomar-submission line for the final compressed
rank-three development. It was created from accepted rank-three checkpoint
`676a335c9a04a7094721b4507914ecfdd1da400d`, not from the later higher-rank
experimental branch. The intended final `v3.0` release commit should be the same
immutable repository snapshot used for Zenodo and Palomar.

## Statement freeze

`Challenge.lean` is the trusted, human-auditable statement surface. It imports only
Mathlib and states only the divisible rank-three theorem corresponding to paper
Theorem 1.2. The unrestricted Kajitani--Ueno--Miyano conjecture is not advertised,
and the paper's full rank-three corollary is not selected because its coprime
ingredient is external literature rather than part of this Lean development.

The established immutable Palomar statement parent is:

`abced491e10f618400e1c9739d2d9503477da76f`

Version-3 CI should reject any drift of `Challenge.lean` from that audited statement
unless a deliberate statement-level revision is made and re-audited from scratch.
Ordinary proof cleanup, paper synchronization, metadata work, or release preparation
must not change the Challenge theorem.

## Palomar surface

- `Challenge.lean`: Mathlib-only advertised statement, with the deliberate registry
  `sorry` standing for the proof to be supplied.
- `Solution.lean`: same statement, proved by a thin wrapper around the substantive
  theorem `Rank3KUM.rankThreeKUM`.
- `comparator.json`: selects only `Rank3KUM.Palomar.rankThreeKUM` and permits only
  `propext`, `Quot.sound`, and `Classical.choice`.
- `formalization.yaml`: v0.4 provenance, scope, automation, review, source,
  fidelity, and alignment metadata. This repository is the substantive
  formalization, not a thin external wrapper.
- `tools/StatementContract.lean`: checks definitional agreement between the
  substantive project theorem and the frozen Palomar statement surface.
- `lakefile.toml`: exposes `Challenge` and `Solution` as Lean library roots.
- `.github/workflows/ci.yml`: builds the release candidate and runs Palomar-oriented
  preflight and Comparator regression checks on `version-3`.

## Verification model

Keep the verification claims separated by scope:

1. Lean elaboration and kernel checking validate the substantive proof and the
   `Solution.lean` wrapper.
2. `#print axioms` records the permitted dependencies
   `[propext, Classical.choice, Quot.sound]` and no `sorryAx` for the proved theorem.
3. `tools/StatementContract.lean` checks the project-to-Challenge statement contract.
4. Comparator checks the selected Challenge/Solution declaration and permitted
   axioms.
5. The repository-local Comparator/NanoDa script is a pinned regression check only.
   Palomar does not delegate NanoDa policy to the submitted configuration: its
   protected verifier forces its own NanoDa replay for every submission.

Do not describe Comparator/NanoDa as an independent replay of unrelated repository
modules. Their selected target is `Rank3KUM.Palomar.rankThreeKUM` and its declaration
closure.

## Version-3 release/submission checklist

Before submitting to Palomar:

1. Freeze one final full 40-character `v3.0` commit SHA. Use that exact SHA for the
   Palomar submission and the software archive; do not submit a branch or tag name.
2. Require green version-3 CI on that exact commit, including the immutable-Challenge
   guard, clean pinned-manifest build, direct Challenge/Solution checks, statement
   contract, and Palomar-oriented Comparator regression.
3. Run the current Palomar production preflight against that immutable commit and
   resolve every mechanical warning or failure.
4. Re-read `Challenge.lean` side by side with version-3 paper Theorem 1.2 and confirm
   all quantifiers, hypotheses, definitions, and scope restrictions still agree.
5. Re-review `formalization.yaml`, especially provenance chronology, AI/human roles,
   review status, DOI references, prior formalizations, and the explicit exclusion
   of paper Corollary 1.3. If the version-3 paper has received a new version DOI by
   then, update the paper source entry before freezing the final commit.
6. Bring `README.md`, `CITATION.cff`, and the paper's formalization appendix into
   agreement with the final v3 commit and version numbers.
7. Confirm there are no new proof-development `sorry`, `admit`, custom `axiom`,
   `unsafe`, `native_decide`, compiled artifacts, submodules, LFS pointers, or
   unpinned/non-public Git dependencies in the submitted snapshot. The deliberate
   Challenge `sorry` is expected and is excluded from the proof-development count.
8. Submit the repository root, the full commit SHA, and `comparator.json` as the
   Comparator configuration path. Leave project/metadata paths at their conventional
   root defaults unless Palomar's interface requires them explicitly.

## Publication boundary

Version 3 remains a rank-three artifact. The later higher-rank generic reduction and
rank-four exploration are not part of this Palomar submission. They should be
migrated to the separate KUM research repository rather than folded into the
Rank3KUM v3 release.
