# Deterministic LUCES reuse: hazard and observable algebra without MT

The finite study demonstrates correct preservation and reuse for deterministic
coupling replacements on the supplied LUCES data. The original PPGraph hazard
and observable-algebra definitions have a checked Lean instantiation.

**It does not demonstrate an operational advantage over the strong ordinary
cache.** Both methods make the same decisions with zero observed wrong
acceptances. PPG is slower in this small workload, including after warming the
caches. The result distinguishes a justified reuse rule from an algorithmic
speedup or a claim that PPGraph is indispensable.

## Scope and fixed inputs

The [plan](PLAN.json) fixes all eight final Paper 3 CSVs and the current
`master-controler/cert_runner` sources, with 36 source/data hashes. The plan
hash is `a3228670c01b9600dd979ce300884efd3ae2d5f0ff52f7d9de17e411edfdf16b`.
This is exploratory work on previously inspected data, not a held-out discovery
experiment. The user's latest instruction explicitly excludes MT here.

The new adapter calls unchanged `_build_bin_distributions`,
`_transport_operator`, `_local_plan_features`, `c_gen` and the shared certificate
AST. For each CSV it uses the first two populated elevation bins and computes
five mixtures of the independent and POT-optimal couplings at fractions
0, 1/4, 1/2, 3/4 and 1. There are **40 computed candidates across eight measured
contexts**. The candidates and proposal schedule are constructed coverage cases;
they are not a historical sequence of controller repairs.

The earlier `build_local_plan_binding` wrapper could not be used unchanged:
it requires GEN PASS and paths inside its own repository. The new adapter
explicitly retains the negative-GEN boot334 context and reads the supplied
Downloads CSVs directly. Neither original producer nor input data was edited.

All 20 nonidentity ordered before/after proposals per context are audited:
**160 proposals per pass**. Seven alternating-order paired repetitions examine
empty and warmed policy caches. Separately, both actual policy implementations
execute the fixed nine-proposal commit/rollback trace in every context.

The maximum checked numerical marginal error is about `2.36e-16`, below the
existing `1e-10` guard. This is numerical evidence, not exact transport feasibility
or verification of POT. Matrices, features, source identities and all eight
indexed check results are in [BANKS.json](evidence/runtime-002/BANKS.json).

## What the two PPG components do

The represented state has four local coupling features plus signed GEN and
the exact integer dataset key. Coupling-only replacement overwrites the first
four and preserves the last two.

### Protected observable algebra

```text
q(snapshot) = (signed GEN, dataset key)

q(replace_local_features(snapshot)) = q(snapshot)
```

This view is **Fixed**, and therefore also Stable, for the modeled operations.
The result covers every rational function-state value in this model, not only
the measured examples. The protected view has eight distinct values over these
40 states, one for each dataset context. It does not decide the complete local
certificate family: Monge, violations and support size still require local data.

### Exact semantic hazard

The source domain is the complete declared list of five snapshots for one
context. The scope consists of certificate positions having a true-before /
false-after witness under that replacement. It is exact for this finite domain,
not for all possible continuous couplings.

All eight contexts have the following scopes for the operation that replaces
the current local fields with candidate j:

| Replacement candidate | Possible invalidated positions |
| --- | --- |
| 0, 1 or 2 | 1, 2, 3, 4, 5 |
| 3 | 2, 3, 4 |
| 4, the optimal candidate | none |

Position 0 is valid rows; 1/5 are repeated Monge; 2 is cycle violations; 3 is
sparsity; 4 is their conjunction; 6 is positive signed GEN; 7 is dataset identity.
Positions remain distinct even when the underlying predicate is repeated.
The scope contains actual witnesses, not just a read/write intersection.
See [HAZARDS.json](evidence/runtime-002/HAZARDS.json).

An empty hazard means that previously true obligations are preserved. It does
not restore previously false ones. Acceptance checks initially failed targets
plus endangered previously true positions. This is equivalent to all eight
holding afterward. Before every scoped decision, the implementation checks
that the before/after snapshots belong to the same declared context bank.

## Formal status and guarantee ledger

[DeterministicReuse.lean](formal/DeterministicReuse.lean) imports the original
`PPGraph.Repair.SemanticHazards` and `PPGraph.Repair.ObservableAlgebra` modules.
Seven printed roots establish:

- protected projection Fixed and Stable;
- finite enumerated scope equal to semantic scope;
- GEN/dataset positions outside the semantic invalidation scope;
- failed-target plus core preservation equivalent to all eight after-checks;
- the original exact-scope acceptance checker realizes that equivalence;
- the original checked step preserves previously passing certificates.

Fresh elaboration passed in **8.506 seconds**, with no warnings/errors; reported
dependencies use only `propext`, `Classical.choice` and `Quot.sound`. This is a
Lean check of the new model wrapper, **not a new Nanoda replay**. The exact
source and logs are retained in [formal-001](evidence/formal-001/RESULT.json).

| Change | Guarantee and remaining obligation |
| --- | --- |
| Four-field snapshot overwrite | GEN/dataset observables are globally fixed in this model. Python/POT producer refinement is not proved. |
| Finite exact scope | Complete-domain proof is list membership. Runtime re-establishes same-context membership; no extension to arbitrary new matrices is inferred. |
| Skipping preserved true positions | Original scope theorem justifies it; failed targets are still checked. |
| Commit/rollback iteration | Accepted states come from the same finite bank; rejected proposals leave the current index unchanged. No general repairability or termination claim follows. |
| Negative GEN context | Preserved as negative. Coupling-only operations cannot make this protected predicate true. |
| MT excluded | These deterministic claims remain. No probabilistic or chain Theta(n) cost guarantee is asserted. |

The formal statement is about rational feature snapshots and their actual
eight predicates. It does not prove that arbitrary Python/POT executions,
floating-point feature extraction, sensor data or physical actions refine them.

## Results and the strong baseline

The ordinary baseline has the same candidates and inputs. It uses exact
coupling-content caching, producer dependencies, and primitive-predicate memo
keys containing predicate identity, exact bound and exact read value. It shares
duplicate Monge predicates and conjunction children, and short-circuits
acceptance. Dataset keys remain full integers, never rounded through float.
Producer and contract identities are fixed and hash-checked for the run.

The PPG arm has the same caches plus complete finite scope preparation and
scoped acceptance. A fresh uncached numerical extraction and original full
checker validate every proposal, independently of both policy caches. This
oracle shares the original numerical producer; it is not an independent
implementation proof of feature extraction.

| Outcome per 160-proposal pass | Ordinary B | PPG |
| --- | ---: | ---: |
| Accepted | 28 | 28 |
| Wrong acceptances under fresh full check | 0 | 0 |
| Wrong scoped omissions | not applicable | 0 |
| Local feature extractions in first empty-cache pass | 40 | 40 |
| Primitive predicate evaluations in that pass | 59 | 61 |

PPG omits 492 position-level obligations per pass using preservation. These are
**not 492 saved expensive computations**: the baseline's ordinary memo already
serves repeated predicate queries cheaply, and scope preparation itself costs
work. PPG performed more primitive evaluations in the first pass.

There are 56 proposal pairs with genuine true-to-false certificate invalidations.
A deliberately unsafe control that retains all previous PASS results makes
28 wrong acceptances. That control shows that invalidation matters; it does
not establish an advantage over the strong safe baseline.

For seven contexts, only candidate 4 satisfies the full family. Boot334 has
signed GEN about `-0.74154`; **none of its five candidates passes all eight**.
It remains in the cohort. No success is manufactured by deleting it or clipping
its signed value to zero. The two policy traces agree over 72 steps each:
14 accepted steps across the seven positive contexts; all boot334 proposals
are rejected. See [TRACES.json](evidence/runtime-002/TRACES.json).

## Cost and ablations

These are median policy times over seven paired repetitions:

| Measured component | Ordinary B | PPG |
| --- | ---: | ---: |
| Preparation plus empty-policy-cache pass | 63.98 ms | 69.97 ms |
| Warm-policy-cache pass | 4.20 ms | 8.42 ms |

The shared input/import/candidate/oracle preparation took 0.647 seconds in the
final process; the shared fresh validation median was 0.238 seconds per pass.
Those costs apply to both arms. The PPG-specific new Lean check adds a one-time
8.506 seconds. The displayed shared preparation includes its measured subparts;
do not add those nested subtimings a second time.

"Empty policy cache" does not mean cold OS, dependencies or process startup.
Including the measured new proof check, PPG wins **0/7 first-use pairs**.
The warm policy is also slower in this finite workload. Earlier dependency,
framework, AI/human and inherited setup costs are not fully measured and are
not treated as zero. No full end-to-end speedup is claimed.

The original `NO_HAZARD` diagnostic prepares the same PPG tables but rechecks
all positions through memoization. It is not an optimized competitor. The
original `NO_OBSERVABLE_REUSE` label also removes hazard selection and clears
the atom cache, while retaining the feature and protected-input preparation.
It is a **joint diagnostic, not an isolated subalgebra ablation**. Its literal
name is preserved in historical outputs, with that limitation stated here.

A separately fixed [supplement](PROTECTED_REUSE_PLAN.json) isolates protected
producer reuse. With the same 160 proposals and unchanged data:

| Producer-only diagnostic | GEN/hash computations | Accepted |
| --- | ---: | ---: |
| Reuse the fixed context value | 8 | 28 |
| Recompute it for every proposal | 160 | 28 |

All produced protected values and decisions agree exactly. The single ordered
timings were about 10 ms versus 140 ms on prepared frames. This is a limited
producer diagnostic, not a robust end-to-end benchmark. Ordinary dependency
caching obtains the same reduction. See
[PROTECTED_REUSE.json](evidence/PROTECTED_REUSE.json).

## A limit on what may be forgotten

Protecting GEN/dataset does not imply that the six-feature snapshot determines
future features under arbitrary matrix mixing. An independently checked exact
rational counterexample uses two constructed 10-by-10 uniform-marginal matrices:

| Matrix | Before: rows, Monge, violations, nnz | After mixing halfway with the same diagonal plan |
| --- | --- | --- |
| A | (10, 49/50, 1, 12) | (10, 99/100, 1, 12) |
| B | (10, 49/50, 1, 12) | (10, 91/100, 1, 12) |

Equal old features lead to unequal new features under the same operation.
Thus that raw feature projection is not universally stable for matrix mixing.
This is a constructed exact-arithmetic guard, not a measured boot witness or
a new Lean theorem. Both new Monge values still pass the 0.69 Boolean cutoff;
the witness concerns feature-update closure, not failure of that predicate.
The protected-view Fixed theorem is unaffected. The
[checker and witness](theory/FEATURE_PROJECTION_COUNTEREXAMPLE.json) retain all
matrices, rational costs, marginals and thresholds.

## Reproducibility and evidence boundaries

The successful main run is [runtime-002](evidence/runtime-002/RESULT.json).
Runtime-001 is retained: its numerical comparison was complete, but its trace
was generated from oracle outcomes rather than by executing each policy. The
archived executor and [revision note](provenance/TRACE_REVISION.json) document
the correction. Runtime-002 factors the common proposal function and executes
both policies' sequential traces. Original inputs, plan and thresholds did
not change. The four malformed-input controls exercise frame/numeric guards;
they are not an end-to-end hostile-input test of an arbitrary controller.

The scientific environment already existed; no package installation or source
modification was required. To repeat with a new output directory:

```sh
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  /Users/gajaka/.local/state/master-controler-study/2026-10-16-b7ca214/python-env/bin/python \
  experiments/luces-deterministic-reuse/run.py \
  --output experiments/luces-deterministic-reuse/evidence/runtime-new
```

No claim here concerns physical controller repair, a new stochastic process,
scientific priority or superiority over all existing methods. The established
result is a checked deterministic preservation rule and a finite operational
comparison in which a strong ordinary cache obtains the same safe decisions
at lower measured policy cost.
