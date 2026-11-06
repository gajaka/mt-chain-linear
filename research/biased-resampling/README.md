# Biased full-footprint resampling

This study formalizes a new redraw law for the existing bridge chain. It
keeps the original states, certificate table and `replace` operation. It does
not modify the registered uniform process or its historical proof receipts.

The fixed-law result and the history-dependent extension are separate.
The proofs count resampling operations, excluding initialization. They do
not bound wall-clock time or establish an advantage over a SAT solver.

## The process and its terminology

There are `n` bridge certificates and `n-1` mutable thresholds. The endpoints
are fixed at `X_0 = 2` and `X_n = 0`. Each internal threshold is in `{0,1,2}`.
Each bridge has one of four raw tactic labels. Label 1, called weak, passes
only when its two thresholds are equal. Each other label, called strong,
passes when its outgoing threshold is at most its incoming threshold.

A failed certificate is a bridge whose local check returns false. Repairing
it overwrites its mutable incoming and outgoing thresholds and its own raw
tactic label. These coordinates form its full footprint. The operation is
the original `MTChainFormal.replace`, including harmless dummy endpoint draws.
All checks must pass for the process to stop.

For a parameter `p`, each fresh mutable threshold has distribution

```text
value             0          1          2
probability    (1-p)/2     (1-p)/2       p
```

The two threshold draws are independent, and the raw tactic is independent
and uniform on four labels. At `p = 2/3` every one of the 36 raw redraws has
positive probability. This is a fixed product resampling law, not rejection
sampling from a collection of preferred outcomes.

## Static theorem

For the fixed repair law `p = 2/3`, the static process selects the least
failed certificate. Its initialization is specified separately:

| Initialization | Formally proved upper bound |
|---|---:|
| Any fixed full state `s` | `6 M(s) + 4 W(s) <= 10n - 6` |
| Original uniform product | `5n - 4` |
| New product with threshold law `(1/6,1/6,2/3)` | `3n - 2` |

Here `M` counts internal thresholds different from 2, and `W` counts weak
raw tactic labels. The raw potential is `V = 6M + 4W`.

Under the new product initialization, for every `n >= 2`,

```text
n/24 <= E[T] <= 3n - 2.
```

`expected_steps_isTheta_linear` proves the corresponding Mathlib `IsTheta`
statement. The sharper lower bound is `(15n - 16)/144`. Its first moment is
`E[D_0] = (15n - 16)/48`; one original update can repair at most three
certificates. The lower bound obtains finiteness from the new upper bound
before taking the vanishing-tail limit.

The original uniform initialization is identified with the old `initialFull`
by the theorem `initialWeight_uniform`. Initialization has not been silently
changed in the `5n - 4` bound.

## History-dependent extension

`HistoryPolicy` supplies two deterministic functions of the current full
state and the entire list of preceding full states, newest first:

1. choose a certificate with a proof that it is failed;
2. choose a parameter in the closed interval `[2/3,1]`.

The subsequent draw is the fresh product law for that parameter. Both
decisions may change after every operation. `adaptiveWork` extends the
history after each redraw and stops on Good; `adaptiveTotalWork` is the
supremum of its finite-horizon costs, defined before finiteness is proved.

For every such policy, every history, every full starting state and `n >= 2`,

```text
E[T] <= V(s) <= 10n - 6.
```

The initialized upper bounds `3n - 2` and `5n - 4` also hold for every policy
in this class. The formal matched lower bound and `IsTheta` theorem in this
package concern the static `p = 2/3` specialization. They are not presented
as a formal all-policy lower-bound theorem.

At `p = 1` the threshold law is degenerate; this endpoint is allowed in the
upper theorem. No uniform Theta(n) claim is made for every matching
initialization in `[2/3,1]`. Additional randomized controller decisions and
arbitrary AI proposal distributions are not directly modeled.

This theorem does not establish that a barrier-position-dependent distribution
outperforms the best static bias, and does not cover policies that use `p < 2/3`
or change the uniform tactic law.

## Why the certificate works

For an interior failed bridge, its old thresholds differ, so at least one
is not 2. The fresh expected number of non-2 thresholds is `2(1-p)`.
For `p >= 2/3`, this decreases the threshold part of the potential by at least
2. The tactic part increases by at most 1 in expectation. The net decrease
is at least 1. The exact worst-case drift bounds are:

| Selected failed bridge | Lower bound on expected decrease |
|---|---:|
| Interior | `12p - 7 >= 1` |
| First | `6p + 3 >= 7` |
| Last | `6p - 3 >= 1` |

These are raw pointwise bounds: they hold in each full state, without
averaging states through a completion law. The raw score need not be zero
on Good; stopping with zero further cost suffices. This proof uses the
ordinary additive-drift argument. It does not reuse the old runtime result.

## Proof map and checks

All names below are in `MTChainFormal.BiasedResampling`.

| File | Role |
|---|---|
| `formal/BiasedDefinitions.lean` | Product weights, score, separate initialization, admissible biases |
| `formal/BiasedLaw.lean` | Normalization, component means, initialization moments |
| `formal/BiasedDrift.lean` | Original coordinate updates and pointwise drift |
| `formal/AdaptiveWork.lean` | Full-history recurrence, infinite budget, static kernel bridge |
| `formal/GenericLower.lean` | Finite-kernel counting lower-bound argument |
| `formal/BiasedLower.lean` | At most three repairs per original footprint update |
| `formal/BiasedResults.lean` | Initialized upper/lower bounds and static Theta(n) |
| `formal/BiasedControls.lean` | Exact counterexamples to invalid proof variants |
| `formal/BiasedAudit.lean` | Independently spelled statements and raw proof-closure axiom audit |

The controls prove that this score fails unit drift under the old uniform
repair law: a genuine active state has score 6 and next expected score 9.
Under the new law its next expected score is 5. Another genuine active
endpoint state proves that omitting the tactic term invalidates the argument.

The verifier rebuilds every study module in a new snapshot, checks the raw
transitive proof closure against only `propext`, `Classical.choice` and
`Quot.sound`, and rejects four negative controls. The injected-axiom control
tests the auditor itself: an extra assumption accepted by Lean as an axiom
must still be rejected by the study's audit. Old runtime modules are excluded
from the mathematical import closure. No new Nanoda replay is claimed.

## Reproduction

Use the root project's pinned Lean 4.35.0 / Mathlib dependencies. If these
are not installed, prepare the root dependency environment first. Then:

```sh
cd research/biased-resampling
lake update
python3 -B verify.py
```

`verify.py` preserves each `.build/attempt-NNN/`, including failures. It
updates `RESULT.json` as an explicitly mutable latest-result summary. Within
the copied workspace only dependency paths in the Lake configuration and
manifest are adapted; mathematical sources are copied verbatim. Pinned
dependency builds are reused, while every local study module is rebuilt.
The replay checks source hashes before and after. No proof receipts in the
original process are rewritten.

## Boundaries

This is a controlled chain with a known easy satisfying configuration. Bias
toward 2 is not a demonstrated general barrier-discovery method. A direct
known-solution overwrite is an important baseline. Smaller upper bounds do
not establish actual speedup, and the user-supplied small-n measurements
have not been reproduced by this formalization.

The original uniform-law potential-class obstruction remains about that
original law. A new small potential does not prove that `(M,W)` is a stable
view supporting autonomous execution. No new application, novelty, practical
PPG superiority, or automatic transfer of the old Theta(n) theorem is claimed.
The discussed Shearer-region obstruction is not mechanized by this package;
its concrete failure probabilities are checked in `BiasedLaw.lean`.

References: [Moser and Tardos](https://arxiv.org/abs/0903.0544) for product
resampling; [Koetzing and Krejca](https://hpi.de/friedrich/docs/publications/2019/TCS_a.pdf)
for drift and hitting-time analysis. These are methodological precedents,
not claims that they already contain this exact chain calculation.
