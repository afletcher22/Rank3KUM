# Rank3KUM compression statement contract

This file records the theorem boundary that structural-compression experiments must preserve.

## Informal theorem being preserved

Let `M` be a finite matroid of rank three whose ground set has cardinality `3k`, with `k > 0`.
Assume `M` is uniformly dense, meaning that every subset `X` of the ground set satisfies

`|X| <= k * r(X)`.

Then the ground set admits a cyclic ordering in which every three cyclically consecutive elements
form a basis of `M`.

This is the divisible rank-three theorem corresponding to Theorem 1.2 of version 2 of
*Cyclic basis orderings of uniformly dense rank-three matroids*.

## Frozen formal surface

The Palomar `Challenge.lean` at immutable parent commit
`abced491e10f618400e1c9739d2d9503477da76f` defines `UniformlyDense`, `cyclicIndex`, and
`CyclicBasisOrder3`, and advertises `Rank3KUM.Palomar.rankThreeKUM` with the same mathematical scope.

The substantive project theorem is `Rank3KUM.rankThreeKUM`. The measurement workflow compiles
`tools/StatementContract.lean`, which checks definitional agreement of the three statement-level
definitions and verifies that the substantive project theorem proves the frozen Palomar theorem under
exactly the advertised hypotheses.

## Scope that must not drift

Compression must not silently strengthen or weaken any of the following:

- ambient rank is exactly three;
- the ground set is finite;
- its cardinality is exactly `3k` with `k > 0`;
- uniform density is required for every subset of the ground set;
- the conclusion enumerates the entire ground set;
- every three cyclically consecutive elements form a basis;
- no simplicity, paving, representability, graphicness, or small-ground-set hypothesis is assumed.

The unrestricted KUM conjecture is not claimed here. The all-cardinality rank-three corollary also
uses the external van den Heuvel--Thomasse nondivisible theorem and is outside this compression
contract.

A change that preserves compilation while changing this scope is statement drift, not proof
compression.
