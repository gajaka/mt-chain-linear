# MT chain: linear cost and restricted drift certificates

This repository contains the original generic MT formalism from `ppg-lean`
and a separate analysis of one concrete resampling chain. The concrete process
has expected redraw count Theta(n), while restricted pointwise-drift
certificates require larger budgets. Scientific novelty remains open.

## Original MT formalism

The original sources are in [library/](library/README.md):

| Theory | Source |
|---|---|
| Product state, footprints and resampling | [Process/Basic.lean](library/PPGraph/MoserTardos/Process/Basic.lean) |
| MT processes and trajectories | [Process/](library/PPGraph/MoserTardos/Process/) |
| Probability and independence | [Probability/](library/PPGraph/MoserTardos/Probability/) |
| Expected cost, drift and termination | [Bounds/](library/PPGraph/MoserTardos/Bounds/) |
| Witness trees and counting | [MoserTardos/](library/PPGraph/MoserTardos/) |
| Hazard and stable observable algebras | [Repair/](library/PPGraph/Repair/) |

All 44 original MT modules and the dependencies needed by these theories are
included with their original source bytes. The library has its own Lake
workspace. The concrete chain's existing Theta(n) proof does not import it;
library availability is not a claim that its general hypotheses have been
instantiated for another repair system.

## Short report

- **Original uniform chain:** for every n>=2,
  `n/18 <= E[T_n] <= 1054*n`, with a proved `IsTheta` statement.
- **Restricted certificates, same uniform law:** both classes have explicit
  certificates for every n>=2. Coordinate-separable active scores require
  exponential normalized initial budget; one bridge per summand requires
  Omega(n^2). The actual process remains Theta(n).
- **Wider local potentials:** seven finite optimum certificates have exact
  primal/dual checks. The width-two all-length Omega(n^2) argument is
  paper-only; its local algebraic identity is checked exactly.
- **Biased law:** static p=2/3 has Theta(n) cost under matching biased
  initialization. Restricted history-dependent choices with p in [2/3,1]
  have linear upper bounds, including `5n-4` under the original uniform start.
- **Negative findings:** the Crew gate did not establish an MT mapping;
  one preselected barrier policy loses to static p=1 for n=2,...,5.

Costs count redraw operations, excluding initialization. These results do not
establish wall-clock speedup, practical PPG superiority, or scientific priority.

## Questions for independent review

1. **Does HLS Theorem 1.6, or another known MT theorem, imply O(n) for this
   exact event system, initialization, scheduler and redraw law?** The scoped
   [literature comparison](research/certificate-existence/LITERATURE.md)
   excludes that particular HLS criterion for the canonical encoding when
   n>=5. The Shearer classification and criterion exclusion are written
   calculations, not separately Lean-checked theorems.
2. **Is the nonvacuous separation between actual linear cost and exponential
   restricted-certificate budget already known?** The precise potential class
   includes a global reset to zero on Good states and full-state pointwise
   drift. The claim restricts potential shape, not additive drift in general.

References or corrections addressing these exact hypotheses are welcome.

## The concrete process

There are n bridges. X_0=2 and X_n=0 are fixed; internal thresholds lie in
{0,1,2}, and each bridge has one of four raw labels. With zero-based indices,

```text
bridge i passes iff
    X_i = X_(i+1)       if R_i = 1 (weak),
    X_(i+1) <= X_i      otherwise (three strong labels).
```

Initialize mutable thresholds and labels independently and uniformly. While
some bridge fails, choose the least failed index and independently redraw
its mutable endpoint thresholds and its own label. Other coordinates remain
fixed. There are 36 raw draws; a fixed-endpoint draw is ignored.
The definitions are in [Chain.lean](formal/mt/core/Chain.lean) and
[ChainKernel.lean](formal/mt/core/ChainKernel.lean). No process step executes
an AI model, Lean tactic or compiler.

The linear upper proof uses permanent barriers and a proved conditional law
of unretained coordinates through observation histories, including rollback.
It is not raw pointwise unit drift for every fixed full suffix. By contrast,
the restricted-certificate lower bounds require drift at every active full
state, averaging only the fresh redraw. Changing the redraw law changes the
comparison; the uniform-law obstructions do not transfer to the biased law.

For the canonical dependency path, endpoint failure marginals are 1/6 and
interior marginals are 5/12. Exact Shearer calculations put n=2,3 inside,
n=4 on the boundary, and n>=5 outside. This does not establish novelty or
exclude every stronger MT criterion. The current lower-bound proof retains
its use of earlier quadratic finiteness.

## Proofs and evidence

| Result | Guide | Verification status |
|---|---|---|
| Concrete Theta(n) | [Core report](REPORT.md) | Lean and Nanoda for selected roots and their proof closure |
| Certificate existence and obstructions | [Certificate study](research/certificate-existence/README.md) | Lean and a separate selected-root Nanoda replay |
| Wider-window hierarchy | [Window locality](research/window-locality/README.md) | Exact finite checks; all-n extension paper-only |
| Biased and history-dependent laws | [Biased study](research/biased-resampling/README.md) | Lean and raw proof-dependency audit; no new Nanoda replay |
| Crew applicability | [Gate report](experiments/crew-mt-applicability/REPORT.md) | Bounded source review, STOP_UNKNOWN |
| Fixed barrier policy | [Exact comparison](experiments/barrier-guided-bias/README.md) | Rational Bellman certificates; no Lean/Nanoda theorem |

Quadratic attainment for the one-bridge and width-two potential classes is
not established. Adaptive-policy upper bounds are not all-policy Theta(n)
claims. The complete package is not covered by one blanket two-kernel audit.

## Build and check

Pinned versions: Lean `leanprover/lean4:v4.35.0`, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
make check
```

The check builds the mathematical workspaces with warnings treated as errors,
validates source identities, verifies all seven window optima and the local
identity, and checks the barrier Bellman certificates. It does not overwrite
historical receipts or perform a fresh Nanoda replay. See [TOOLING.md](TOOLING.md)
for independent-checker versions, allowed axioms and fresh replay commands.

`formal/`, `research/`, and `library/` contain the mathematics. `scripts/`,
`tooling/`, and `evidence/` support verification. The small
[provenance/](provenance/README.md) directory contains original source versions
required by the existing source validators. Build caches and raw exports are
ignored by Git; replaying historical receipts may require local artifacts
or a fresh run. Internal cleanup logs and workspace notes are not published
as part of this package.

Kernel acceptance, correspondence to an external implementation, and priority
are separate questions. See [dependency and source notices](THIRD_PARTY_NOTICES.md).
