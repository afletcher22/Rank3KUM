# Palomar Registry preparation

This branch packages the substantive Rank3KUM development for a Palomar Registry submission.
It was branched from `version-2`; the mathematical Lean sources inherited from that branch are
unchanged by the initial Palomar packaging commits.

## Statement freeze

`Challenge.lean` is the trusted, human-auditable statement surface. It imports only Mathlib and
states only the divisible rank-three theorem corresponding to paper Theorem 1.2. The unrestricted
Kajitani--Ueno--Miyano conjecture is not advertised, and the paper's full rank-three corollary is
not selected because its coprime ingredient is external literature rather than part of this Lean
development.

Once the Challenge has passed the statement audit, proof-engineering or structural-compression
work should normally change the substantive proof and/or `Solution.lean`, not `Challenge.lean`.
Any later Challenge change should be treated as a statement-level change and re-audited against
the paper from scratch.

## Palomar surface

- `Challenge.lean`: Mathlib-only advertised statement.
- `Solution.lean`: same statement, proved by a thin wrapper around `Rank3KUM.rankThreeKUM`.
- `comparator.json`: selects `Rank3KUM.Palomar.rankThreeKUM` and permits only
  `propext`, `Quot.sound`, and `Classical.choice`.
- `formalization.yaml`: v0.4 provenance, scope, automation, review, source, and alignment metadata.
- `lakefile.toml`: exposes `Challenge` and `Solution` as Lean library roots.
- `.github/workflows/ci.yml`: builds the Palomar targets on this branch and checks both modules
  directly with Lean.

## Before submission

1. Require a green clean CI build of the exact candidate commit.
2. Run the official Palomar preflight/Comparator path against that immutable commit and resolve
   every mechanical warning or failure.
3. Confirm Comparator accepts the Challenge/Solution pair and reports only the permitted axioms;
   Palomar will independently force NanoDa checking during verification.
4. Re-read `Challenge.lean` side by side with paper Theorem 1.2 and confirm all quantifiers,
   hypotheses, definitions, and scope restrictions still agree.
5. Re-review `formalization.yaml`, especially source/provenance chronology, automation details,
   review status, DOI references, and the explicit exclusion of paper Corollary 1.3.
6. Confirm there are no new `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, compiled
   artifacts, submodules, LFS pointers, or unpinned/non-public Git dependencies in the submitted
   snapshot.
7. Submit the full 40-character commit SHA and `comparator.json`; do not submit a branch name as
   the registry revision.
