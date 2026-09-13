# Compression exploration baseline

This directory records the measurement contract for structural-compression experiments on
`Rank3KUM.rankThreeKUM`.

## Immutable starting point

- Parent branch: `palomar`
- Parent commit: `abced491e10f618400e1c9739d2d9503477da76f`
- Mathematical target: `Rank3KUM.rankThreeKUM`
- Frozen Palomar statement surface: `Challenge.lean`
- Paper statement: Theorem 1.2 of *Cyclic basis orderings of uniformly dense rank-three matroids*, version 2

Palomar wrapper files, metadata, Comparator configuration, and CI infrastructure are verification
scaffolding. They are not mathematical compression targets.

## Mechanical measurement only

The dependency map is deliberately syntactic and reproducible. It asks:

> Which project-owned declarations are reachable from `Rank3KUM.rankThreeKUM` through constant
> occurrences in declaration types, opaque-inclusive values, or inductive/constructor/recursor
> metadata?

Project ownership is determined by defining-module provenance (`Rank3KUM` or `Rank3KUM.*`), not by
declaration namespace. This prevents the measurement tool itself, private names, or namespace changes
from contaminating project ownership.

The extractor records type, value, and declaration-metadata dependencies separately and also records
their union. Missing project-owned dependencies are fatal in the postprocessor.

## What the metrics do and do not mean

The active transitive closure is a formal dependency inventory, not a direct count of mathematical
ideas or irreducible proof steps. In particular:

- `Name.isInternal` is reported literally and is not called an authored/generated classification;
- constructor and recursor metadata are included, so datatype packaging can produce structural SCCs;
- maximum shortest distance from the root and longest SCC-condensation path are reported separately;
- fan-in, fan-out, one-incoming-edge flags, and node counts are descriptive graph facts;
- equation lemmas, matchers, constructors, recursors, and likely projections are conservatively
  attributed to an origin declaration when recognizable, but these origin hints are explicitly
  heuristic and are not a compression score.

A later claim of structural compression should therefore distinguish at least three things:

1. changes to the raw kernel/declaration graph;
2. changes after conservative generated-helper aggregation;
3. removal or simplification of actual mathematical obligations.

No single scalar metric is treated as sufficient evidence of proof simplification.

## Reproducibility and drift guards

The workflow:

- compares `Challenge.lean` to the immutable parent commit rather than to a moving branch;
- uses the committed `lake-manifest.json` and does not run `lake update` in the measurement job;
- records the current source commit, Lean toolchain/version, dependency revisions, manifest hash,
  Challenge/Solution hashes, and measurement-tool hashes in the artifact;
- compiles `tools/StatementContract.lean` to check definitional agreement between the substantive
  project definitions/theorem and the frozen Palomar surface;
- runs the Palomar-pinned Comparator and NanoDa replay independently.

The generated artifact is `rank3kum-mechanical-proof-map-v2`.
