# Compression exploration baseline

This directory records the immutable starting point for structural compression experiments on
`Rank3KUM.rankThreeKUM`.

## Baseline

- Parent branch: `palomar`
- Parent commit: `abced491e10f618400e1c9739d2d9503477da76f`
- Mathematical target: `Rank3KUM.rankThreeKUM`
- Palomar statement surface: `Challenge.lean`
- Paper statement: Theorem 1.2 of *Cyclic basis orderings of uniformly dense rank-three matroids*, version 2, DOI `10.5281/zenodo.22698709`

The Palomar-specific wrapper, metadata, Comparator configuration, and CI machinery are surrounding
verification infrastructure. They are not optimization targets and are excluded from compression
metrics unless explicitly stated otherwise.

## Epistemic layers

Compression work must keep three layers separate:

1. **Mechanical facts.** Kernel declaration dependencies, module provenance, graph reachability,
   import edges, declaration kinds, graph statistics, and other data extracted without mathematical
   interpretation.
2. **Semantic annotations.** AI- or human-proposed descriptions of what a mechanically identified
   region is doing mathematically. These are hypotheses about the artifact, not mechanical facts.
3. **Compression hypotheses.** Proposals that a region can be replaced, deleted, generalized, or
   reorganized. These require experiments and must not be inferred merely from graph shape.

The mechanical baseline is generated before semantic annotation.

## Statement-drift rule

`Challenge.lean` is frozen during compression exploration. The compression workflow checks that it
has no diff from the `palomar` branch. A change to the advertised statement is therefore a separate
statement-level event, not a compression step.

The corresponding informal/formal contract is recorded in `STATEMENT_CONTRACT.md`. Every proposed
architectural rewrite must continue to prove the same theorem under the same definitions and scope.
If a change appears to require modifying the statement contract, compression stops and the change is
reviewed as a theorem-scope change instead.

## What is measured

The primary structural score is computed only on the transitive project-local dependency closure of
`Rank3KUM.rankThreeKUM`. In particular, Palomar wrappers and registry files do not count toward
mathematical compression.

The baseline extractor records:

- every imported `Rank3KUM.*` declaration and its declaration kind;
- direct project-local declaration dependencies;
- external dependency boundary names;
- declaration-to-module provenance;
- the active transitive closure of `Rank3KUM.rankThreeKUM`;
- declarations outside that closure;
- fan-in, fan-out, root depth, SCCs, and one-use-chain candidates;
- module-level dependency edges induced by active declarations; and
- source-level Lean import edges.

These measurements are descriptive. A high fan-out declaration is not automatically important, and
an inactive or one-use declaration is not automatically redundant.
