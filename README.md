# Linear expected resampling cost for a finite MT chain

The active project is `mt-chain-linear`. Its concrete chain study concerns one
explicitly defined Moser-Tardos (MT)
resampling process. Under its independent product initialization, its expected
number of resampling operations is Theta(n):

```text
For every n >= 2:

    n/18 <= E[T_n] <= 1054*n.
```

This is an ideal process bound, not compiler, AI-prover or seeded-PRNG timing.
The chain proof was extracted from `../ppg-proof-repair`. Its mathematical
import closure remains independent of PPGraph. The project also restores the
original MT, probability, hazard and observable-subalgebra framework from
`../ppg-lean` as a local library copy. No scientific novelty is claimed here.

## Original framework in the active project

`vendor/ppg-lean` contains the original library, copied rather than moved from
`../ppg-lean`. The separate Lake workspace in `framework/` uses that local
dependency, making its definitions and theorems available in this same project.
The root chain workspace retains its existing dependency manifest.

The restoration is verified: 228 original files match byte-for-byte, all 208
library modules build, and the fresh reported-axiom audit covers 5,835 owned
declarations using only the three standard axioms. See the
[framework report](framework/REPORT.md) and its linked receipts. This new check
is not a Nanoda replay or a Crew instantiation.

| Local library area | Role |
| --- | --- |
| `PPGraph/MoserTardos/Process/` | MT states, local resampling, trajectories and random initialization |
| `PPGraph/MoserTardos/Probability/` | Product-log probability laws and measurable events |
| `PPGraph/MoserTardos/Bounds/` | Expected-step, termination, drift and additive-cost results under their stated hypotheses |
| `PPGraph/Repair/Hazards.lean` and `SemanticHazards.lean` | Footprint locality and exact semantic invalidation scope |
| `PPGraph/Repair/ObservableAlgebra.lean` | Stable observable subalgebras, retained information and deterministic quotients |
| `PPGraph/Repair/ObservableKernel.lean` | Kernel closure, fiber transition laws and good-state locality |

These paths are relative to `vendor/ppg-lean`. Original source identities and
licenses are preserved with the copy. Availability of this library does not
instantiate its hypotheses for a new program: an actual application still
needs its state space, repair operations, probability law, certificate
predicates, hazard correspondence and observable reduction justified.

The Kiro Crew actual-code reproduction remains in
`../ppg-proof-repair/experiments/kiro-crew-comparison`; it is not currently being
extended. That reproduction does not execute an MT repair process or establish
a PPG controller advantage. Restoring this framework does not transfer the
chain's Theta(n) bound to Crew, Python tests, adaptive AI proposals or another
repair process. New framework-import checks are separate from the recorded
chain verification below.

## The process

Bridge i joins X_(i-1) to X_i with label R_i. There are n bridges.
Here indices are one-based; Lean's `Fin n` bridge indices are zero-based.

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

The definition models a finite measured Lean-tactic table. It is not a universal
description of Lean tactics; a process step invokes no tactic or compiler.

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
`HistoryFiltering.lean` proves that law for every positive-probability history
ending actively under the registered initialization, including rollback histories.

Regular steps pay at least one unit of potential. For exceptional steps, an
expected barrier advance of at least 1/4 pays for local growth bounded by 243:
`1000/4 - 243 = 7`. The observed potential is nonnegative, at most `1054*n`,
and zero at termination. Kernel transport and the infinite-horizon supremum
then yield the upper bound.

The extraction retains the earlier quadratic proof machinery: the present
lower-bound proof uses finiteness/survival lemmas from `FinalQuadratic.lean`.
It does not remove every dependency on that earlier argument.

## Main declarations and source layout

Principal namespaces are `MTChainFormal` and `MTChainFormal.Tightness`.

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
| `vendor/ppg-lean/` | Local copy of the original MT, probability, hazard and observable framework |
| `framework/` | Separate Lake workspace and import audit for the restored original library |

`SOURCE_MANIFEST.json` preserves the original extraction identities and adaptations.
The extracted versions are archived under `provenance/module-migration/before/`.
`MODULE_MIGRATION.json` records the later module-system migration and current
source identities. The source project is needed only for optional comparison.
Historical and current verification evidence are kept separately.

## Build and verification

Use the toolchain pinned in `lean-toolchain` and the committed Lake manifest.
The root Lake workspace keeps pinned Mathlib as its only direct library
dependency. The `framework/` workspace separately depends on the local original
PPGraph library in `vendor/ppg-lean`. This preserves both the root manifest and
the concrete chain's separate raw MT proof closure.

```sh
lake exe cache get
lake --wfail build
python3 scripts/verify.py --output evidence/source-check-local.json
```

To check both workspaces, use the repository-level entry point:

```sh
make check
```

The framework check is also available as `python3 framework/check.py`. Its
evidence concerns the copied original library and its import audit; it is
separate from the existing chain/Nanoda evidence and from a Crew instantiation.

When the source project is available, source identity can also be checked with:

```sh
python3 scripts/verify.py --compare-source ../ppg-proof-repair --output evidence/source-comparison-local.json
```

Recorded chain verification after the module-system migration:

The following counts describe the chain audit before the framework restoration.
They do not certify the new library-import target or an external implementation.

- All 34 local Lean modules built from an absent project build directory;
  `lake --wfail build` reported zero warnings and zero errors. Pinned external
  dependency caches were reused.
- The 32 archived extraction copies match their source SHA-256 values.
  Current proof files have only the recorded module-header changes; their
  mathematical bodies are unchanged. The optional comparison also checks
  81 source-project files/configurations unchanged.
- Nine selected theorem statements, binders and actual proof closures passed
  the axiom audit, using only `propext`, `Classical.choice` and `Quot.sound`.
- A fresh Nanoda replay checked those nine roots and their proof closure:
  17,707 expanded declarations, with no errors and no PPG imports in that
  chain proof closure.

See [REPORT.md](REPORT.md) and [evidence/VERIFICATION.json](evidence/VERIFICATION.json).
The original build produced 23 Lake module-migration warnings. The proof files
now use `module`, `public import` and `@[expose] public section`, preserving
public definitions and transitive imports. No warning category is suppressed.
The audit separately loads full private proof data so module visibility cannot
hide a proof body from its transitive axiom check. The initial failed strict
build and the earlier successful verification remain historical evidence.

[TOOLING.md](TOOLING.md) documents the external checker, its binary-specific
pins and the exact replay commands. A saved-evidence check on the current
local artifacts is:

```sh
python3 -B scripts/independent.py --verify --attempt attempt-003
```

Raw exports and compiled dependencies are excluded from Git. A fresh checker
run requires those tools and a new unused attempt name. `verify.py` writes a
new source receipt and refuses to overwrite an existing file; choose an unused
`--output` path on each run. Independent proof attempts are also never overwritten.
These checks concern the formal definitions, not an
external Python implementation or a random-number generator.

## Research: which potentials can explain the linear cost?

The separate [certificate-existence study](research/certificate-existence/README.md)
constructs admissible potentials for every `n >= 2` and proves an exponential
budget lower bound for the coordinate-separable class, despite the same process
having expected cost Theta(n). The larger one-bridge-per-summand class is also
proved inhabited; its existing quadratic lower bound remains, without a matching
quadratic upper construction. Nine research roots have a fresh Lean/Nanoda audit.

This is a restriction on certificate shape and raw pointwise drift, not a lower
bound on all drift analyses or evidence of a faster algorithm. The child package
has its own manifest and evidence, and leaves the original proof core unchanged.

The follow-up [window-locality study](research/window-locality/README.md)
computes exact minimum budgets for two-bridge summands at n=3,4,5,6. An exact
local witness also supports an all-n quadratic obstruction for that wider
class. Its all-n gauge/flux argument is currently paper-only, awaiting Lean;
the finite optima have independent rational primal/dual checks.

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
The [research comparison](research/certificate-existence/LITERATURE.md)
gives a separate exact-rational exclusion of that criterion for this encoding
when n >= 5; that argument has not been formalized in Lean here.
Being outside the classical region also does not establish scientific novelty.

- [Moser-Tardos: constructive LLL, Theorem 1.2](https://arxiv.org/abs/0903.0544)
- [Kolipaka-Szegedy: STOC 2011 official abstract](https://acm-stoc.org/stoc2011/AcceptedPapersWithAbstracts.htm)
- [He-Li-Sun: graph-uniform versus intersection-sensitive criteria](https://arxiv.org/abs/2111.06527)

Prior formalizations also preclude a first-LLL/first-MT-formalization claim:

- [Chelsea Edmonds: AFP Lovasz Local Lemma](https://isa-afp.org/entries/Lovasz_Local.html), covering classical existence statements.
- [Edouard Bonnet: Lean MT proof source](https://github.com/EdouardBonnet/moser-tardos/blob/b3856214a13da34e584db6c404622651c1581835/proofs/Lax965890Proofs/MoserTardos.lean#L2086), not independently replayed by this extraction.

No arbitrary warm-start, alternative scheduler, adaptive AI guarantee, practical
proof-repair speedup or uniqueness of this proof method is established here.
The open comparison is whether a known theorem already implies Theta(n) for
this exact event system, product law, least-failed rule and full local redraw.
See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for provenance and licenses.
