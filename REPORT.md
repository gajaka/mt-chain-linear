# Finite MT chain: process and linear expected cost

This report specifies the concrete process and its expected-cost theorem.
For every n>=2, under independent uniform product initialization,

```text
(5*n-6)/36 <= E[T_n],
n/18 <= E[T_n] <= 1054*n,
E[T_n] = Theta(n).
```

T_n counts redraw operations, excluding initialization. The bound does not
charge for scanning to find a failure, individual random bits, or compiler
execution. An operation returning the previous coordinate values still costs
one. No wall-clock speedup or scientific priority is claimed.

## Process

There are n bridges with mutable thresholds X_1,...,X_(n-1) in {0,1,2},
fixed endpoints X_0=2 and X_n=0, and labels R_0,...,R_(n-1) in {0,1,2,3}.
Bridge i passes exactly when

```text
X_i = X_(i+1)       if R_i = 1 (weak),
X_(i+1) <= X_i      otherwise (three strong labels).
```

All mutable thresholds and labels start independently and uniformly. At an
active state, choose the least failed index i and independently redraw the
mutable coordinates among X_i, X_(i+1), R_i. Other coordinates remain fixed.
The formal operation averages 36 uniform raw triples; a fixed-endpoint draw
is ignored. Good configurations stop at cost zero.

The expected total work is an extended nonnegative expectation, defined as
the supremum of finite-horizon accumulated active-state costs. Its finiteness
is a proved conclusion, not a premise.

## Why the cost is linear

The lower bound uses the exact initial first moment

```text
E[initial failed bridges] = (5*n-6)/12.
```

One operation can remove at most three current failures: the selected bridge
and its two neighbors. Therefore `E[T_n] >= (5*n-6)/36 >= n/18` for n>=2.
The current lower-bound proof uses the established quadratic finiteness result
before taking a vanishing-tail limit.

The upper bound uses a retained-prefix observation and the potential

```text
V = 1000*(n-F) + B,
B = 35*d + 2*r + 33*[r>0].
```

F is a permanent barrier height, d a retained distance, and r a trailing
zero-run length. A barrier combines a passing prefix, incoming threshold 2,
and a strong label. Their exact definitions are in
[Features.lean](formal/mt/core/Features.lean).

The proof establishes the conditional completion law of unretained coordinates
for every relevant positive-probability observation history, including rollback.
Under this law, regular steps pay at least one unit of potential. Exceptional
steps have expected barrier advance at least 1/4 and local growth at most 243;
the barrier term pays `1000/4-243=7`. The observed potential is nonnegative,
zero at termination, and at most 1054*n. Kernel transport and the infinite-
horizon supremum give the linear upper bound.

This is completion-averaged drift under a proved conditional law, not raw
pointwise unit drift for every arbitrarily fixed full suffix.

An invalidation is a passing bridge becoming failing in one operation.
Only two neighbors can be newly invalidated, hence `E[I_n] <= 2108*n`.
Repeated episodes count separately; no matching lower bound is asserted.

## Main declarations

The theorem namespace is `MTChainFormal.Tightness`.

| Source | Principal content |
|---|---|
| [Chain.lean](formal/mt/core/Chain.lean), [ChainKernel.lean](formal/mt/core/ChainKernel.lean) | States, local update, least-failed kernel, initialization and counted work |
| [HistoryFiltering.lean](formal/mt/core/HistoryFiltering.lean) | Conditional completion law through observation histories |
| [LowerBound.lean](formal/mt/tightness/LowerBound.lean) | `expected_steps_ge_linear_refined`, `expected_steps_ge_linear` |
| [LinearPotential.lean](formal/mt/tightness/LinearPotential.lean) | `expected_steps_le_linear`, `expected_invalidations_le_linear` |
| [LinearAsymptotics.lean](formal/mt/tightness/LinearAsymptotics.lean) | `expected_steps_isTheta_linear` |
| [TightnessResults.lean](formal/mt/tightness/TightnessResults.lean) | `linear_work_bounds` and exclusion of an eventual positive quadratic lower bound |

The general MT framework in [library/](library/README.md) has its own stated
hypotheses. The chain theorem is proved through its explicit finite kernel;
it is not asserted as a new automatic instantiation of every framework result.

## Recorded verification

The [aggregate receipt](evidence/VERIFICATION.json) records:

| Check | Result |
|---|---|
| [Strict build](evidence/lean-build-005/RESULT.json) | PASS, 34 local modules, zero warnings and errors |
| Selected theorem types, binders and actual proof dependencies | PASS, nine roots |
| Raw transitive kernel closure | 17,247 declarations |
| [Independent Nanoda replay](evidence/attempt-003/RESULT.json) | PASS, 17,707 expanded declarations |
| Permitted transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |

The raw-kernel and expanded-export inventories use different counting
conventions. Nanoda covers the nine selected roots and their proof closure,
not every assertion in every source module. These recorded checks are not a
claim that a fresh second-kernel run occurs on every build. Source checks
and [rejected validation controls](evidence/module-migration-validator-controls.json)
support the identity of the audited inputs.

Pinned tools are Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Run `make core` for the strict chain
build, or `make check` for the project's mathematical checks. [TOOLING.md](TOOLING.md)
describes independent replay, exact tool identities and resource settings.

## Interpretation and literature boundary

For the canonical dependency path, endpoint failure marginals are 1/6 and
interior marginals are 5/12. Exact Shearer-polynomial calculations classify
n=2,3 inside the region, n=4 on the boundary, and n>=5 outside. The separate
[HLS Theorem 1.6 comparison](research/certificate-existence/LITERATURE.md) is
also a written exact-arithmetic argument. Neither comparison is a separately
Lean/Nanoda-checked theorem here, and neither excludes all existing MT criteria.
Whether the linear bound or the restricted-certificate separation follows
from prior work remains a question for independent mathematical review.
