# Linear expected resampling cost for a finite MT chain

This standalone Lean project studies one explicitly defined Moser-Tardos (MT)
resampling process. Under its independent product initialization, its expected
number of resampling operations is Theta(n):

```text
For every n >= 2:

    n/18 <= E[T_n] <= 1054*n.
```

The result concerns an ideal finite stochastic process, not the running time of
a Lean compiler, an AI prover, or an implementation using a seeded PRNG.
It is extracted from the chain analysis in `../ppg-proof-repair`; PPGraph is
not a dependency of this package. Scientific novelty is not claimed.

## The process

There are n local obligations, called bridges. Bridge i connects thresholds
X_(i-1) and X_i and carries a label R_i. Indices here are one-based; Lean's
`Fin n` bridge indices are zero-based.

```text
    2 = X_0 -- R_1 --> X_1 -- R_2 --> ... -- R_n --> X_n = 0

    X_1, ..., X_(n-1) : independent uniform values in {0,1,2}
    R_1, ..., R_n     : independent uniform labels in {0,1,2,3}
```

All threshold and label coordinates are initially independent. A bridge passes
according to `MTChainProof.bridgePass` in `FreshDraws.lean`:

```text
    R_i = 1       : passes exactly when X_(i-1) = X_i
    R_i in {0,2,3}: passes exactly when X_i <= X_(i-1)
```

The table originated in a finite Lean-tactic experiment. Here it is a
mathematical definition. These proofs do not establish a universal description
of Lean tactics, and a process step does not invoke a live tactic or compiler.

```text
    Initialize all mutable coordinates from the product law.
    While some bridge fails:
        i := the smallest index of a failing bridge
        independently redraw the mutable coordinates in {X_(i-1), X_i, R_i}
    Stop when every bridge passes.
```

Fixed endpoints are never changed. The formal update uses 36 equally weighted
triples in `{0,1,2} x {0,1,2} x {0,1,2,3}`. At an endpoint one threshold draw is
ignored, so the same law has 12 equally weighted effective updates there.
A redraw counts as one operation even if it returns the previous values.

## What is counted

`expectedSteps n` is an extended nonnegative expectation, defined as the
supremum of finite-horizon accumulated active-state costs. Each active update
costs one; terminal states cost zero. Good configurations are collapsed to a
single absorbing terminal state in the kernel representation.

The initial product sample is excluded from T_n. Neither checking all bridges
to find the least failure nor drawing individual coordinates is separately
charged. The theorem therefore gives an operation count, not a wall-clock or
bit-complexity bound. Finiteness is a proved conclusion, not a premise.

An invalidation means a passing bridge becomes failing in one update. Repeated
passing-to-failing episodes for the same bridge count separately. Only the two
neighbors of the selected failing bridge can be newly invalidated, giving the
additional upper bound `E[I_n] <= 2108*n`; no matching lower bound is claimed
for invalidations.

## Why the expected cost is linear

The lower bound uses the exact initial first moment:

```text
    E[number of initially failing bridges] = (5*n - 6)/12.
    One update can remove at most three currently failing bridges.
    Hence E[T_n] >= (5*n - 6)/36 >= n/18, for n >= 2.
```

The upper bound uses permanent barriers and an explicit potential:

```text
    V = 1000*(n - F) + B
    B = 35*d + 2*r + 33*[r > 0]
```

F is the permanent barrier height, d is a retained-prefix distance, and r is
the trailing zero-run length. Their exact definitions are in `Features.lean`.
The retained observation includes the inspected coordinates through the first
failed bridge; bridges strictly before it are passing.

The crucial drift is averaged using the proved conditional completion law of
the unretained coordinates. It is not a raw pointwise drift claim for every
arbitrary fixed suffix. The `actual_history_fresh_tail` theorem in
`HistoryFiltering.lean` proves that law after every positive-probability observation
history under the registered initialization, including histories with rollback.

Regular steps pay at least one unit of potential. For exceptional steps, an
expected barrier advance of at least 1/4 pays for local growth bounded by 243:
`1000/4 - 243 = 7`. The observed potential is nonnegative, at most `1054*n`,
and zero at termination. Kernel transport and the infinite-horizon supremum
then yield the upper bound.

The extraction retains the earlier quadratic proof machinery. In particular,
the present lower-bound proof uses the established finiteness/survival lemmas
from `FinalQuadratic.lean`. This is not presented as a new independent proof
architecture that removes every dependency on that earlier argument.

## Main declarations and source layout

All principal declarations use namespace `MTChainFormal`, with linear results
in `MTChainFormal.Tightness`.

| File | Role |
| --- | --- |
| `formal/mt/core/Chain.lean` | Raw states, bridge validity, least-failed selection, local update |
| `formal/mt/core/ChainKernel.lean` | Uniform update kernel, product initialization, invalidation count |
| `formal/mt/core/HistoryFiltering.lean` | Conditional law after complete finite observation histories |
| `formal/mt/core/FinalQuadratic.lean` | Expected-cost definition and earlier quadratic/finiteness results |
| `formal/mt/tightness/LinearPotential.lean` | `expected_steps_le_linear` and linear invalidation upper bound |
| `formal/mt/tightness/LowerBound.lean` | `expected_steps_ge_linear_refined` and `expected_steps_ge_linear` |
| `formal/mt/tightness/LinearAsymptotics.lean` | `expected_steps_isTheta_linear` |
| `formal/mt/tightness/TightnessResults.lean` | Standalone result wrapper, adapted to remove PPG integration |
| `formal/mt/paper/` | Separate accounting/barrier supplement; not a premise of Theta(n) |
| `formal/theta-audit/` | Independent-checker quotation support |

`SOURCE_MANIFEST.json` identifies exact copies and adaptations. The source project
is needed only for optional comparison. Historical and fresh evidence differ.

## Build and verification

Use the toolchain pinned in `lean-toolchain` and the committed Lake manifest.
The only direct library dependency is the pinned Mathlib revision.

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

When the source project is available, source identity can also be checked with:

```sh
python3 scripts/verify.py --compare-source ../ppg-proof-repair
```

Independent verification uses `scripts/independent.py`; consult its `--help`
for the required external checker configuration. Fresh build and checker
receipts belong under `evidence/`. At extraction time fresh verification is
pending: old Lean/Nanoda results are not silently promoted to new-package passes.
The build verifies proofs about these definitions; it does not validate an
external Python implementation or a random-number generator.

## Relation to existing MT results

Under the classical MT criterion, the known expected bound is
`sum_i x_i/(1-x_i)`. Kolipaka-Szegedy gives `n/epsilon` when
`(1+epsilon)*p` remains inside Shearer's region. Uniform linearity requires
controlled weights or slack; mere interior membership does not suffice.

Here endpoint bad-event probabilities are 1/6 and interior probabilities are
5/12. Their canonical variable-dependency graph is a path. Direct Shearer
polynomials put n=2,3 inside, n=4 on the boundary, and n>=5 outside.
Chordal-graph tightness concerns guarantees for all realizations with the same
graph and probabilities, not the speed of this particular realization.

HLS Theorem 1.6 uses actual event intersections and must be considered
separately; the fact that a path is chordal does not itself exclude it.
Being outside the classical region also does not establish scientific novelty.

- [Moser-Tardos: constructive LLL, Theorem 1.2](https://arxiv.org/abs/0903.0544)
- [Kolipaka-Szegedy: STOC 2011 official abstract](https://acm-stoc.org/stoc2011/AcceptedPapersWithAbstracts.htm)
- [He-Li-Sun: graph-uniform versus intersection-sensitive criteria](https://arxiv.org/abs/2111.06527)

No arbitrary warm-start, alternative scheduler, adaptive AI generator, practical
proof-repair speedup, or uniqueness of this proof method is established here.
See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for provenance and licenses.
