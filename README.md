# MT chain: linear cost and restricted drift certificates

This project studies one explicitly defined Moser-Tardos (MT) resampling
process. Its central result compares the actual expected redraw count,
Theta(n), with the larger budgets required by restricted drift certificates.
Scientific novelty remains a question for independent expert review.

## Short report and questions for reviewers

For the original uniform product law and least-failed local redraw rule, we
prove `n/18 <= E[T_n] <= 1054*n` for every n>=2. For the SAME process and
initialization, every nonnegative stopped potential with a coordinate-separable
active score and uniform positive raw pointwise drift has an exponential
normalized initial budget. The class is constructively inhabited for every
n>=2. The larger one-bridge-per-summand class is also inhabited and has an
Omega(n^2) lower budget. The main claims have Lean proofs and independent
Nanoda replays of selected roots and their actual proof closures.

Separate results cover a biased redraw law and restricted history-dependent
policies (Lean/audit), finite wider-window optima (exact rational checks),
and a width-two all-length obstruction (paper-only). The Crew applicability
gate remained inconclusive, and one preselected barrier policy lost to a
static bias. These findings do not establish a faster practical algorithm.

We would appreciate references or a correction on two questions:

1. **Does HLS Theorem 1.6, or another existing MT theorem, imply O(n) for this
   exact event system, initialization, scheduler and redraw law?** Our scoped
   [comparison](research/certificate-existence/LITERATURE.md) excludes that
   particular HLS criterion for the canonical encoding when n>=5. The Shearer
   classification and criterion exclusion are written calculations, not
   separately Lean-checked theorems.
2. **Is this nonvacuous separation between actual linear cost and exponential
   restricted-certificate budget already known?** The precise class includes
   the global Good reset and full-state pointwise drift. The claim concerns
   potential shape, not additive drift analysis in general.

No priority claim is made. Reproduction commands, exact definitions and
evidence boundaries follow below; further context is in the
[certificate-study report](research/certificate-existence/REPORT.md).

## Package overview

The active branch contains five parts:

| Part | Result | Evidence |
|---|---|---|
| Original uniform chain | n/18 <= E[T] <= 1054*n for n >= 2 | Lean; Nanoda replay of selected roots and their proof closure |
| Restricted certificates under that uniform law | Constructive existence; exponential lower budget for coordinate-separable active scores; Omega(n^2) for one bridge per summand | Lean; separate Nanoda replay of selected roots and their proof closure |
| Wider local potentials | Seven exact finite optima; a width-two all-length Omega(n^2) obstruction | Independent rational checks for finite certificates and a local identity; the all-length argument is paper-only |
| Biased resampling | Static p=2/3 has Theta(n) cost under matching initialization; restricted history-dependent policies have linear upper bounds | Lean and raw proof-dependency audit; no new Nanoda replay |
| Negative findings | Crew MT correspondence unresolved; one fixed barrier policy loses to a valid static bias for n=2,...,5 | Bounded source gate; independent exact rational calculation |

All costs count resampling operations, excluding initialization. They are
not compiler, AI-prover, random-bit, or wall-clock complexity bounds.

## The original process

There are n bridges with fixed endpoints X_0=2 and X_n=0. Mutable thresholds
X_1,...,X_(n-1) lie in {0,1,2}; labels R_0,...,R_(n-1) lie in {0,1,2,3}.
Using zero-based bridge indices:

```text
bridge i passes iff
    X_i = X_(i+1)       if R_i = 1 (weak),
    X_(i+1) <= X_i      otherwise (three strong labels).
```

Initialize all mutable coordinates independently and uniformly. Until all
bridges pass, choose the least failed bridge and independently redraw its
mutable endpoint thresholds and own label. Other coordinates stay fixed.
The formal operation averages 36 raw draws; a fixed-endpoint draw is ignored.

[Chain.lean](formal/mt/core/Chain.lean) defines the states and update;
[FreshDraws.lean](formal/mt/core/FreshDraws.lean) defines the pass table.
The mathematical process itself invokes no Lean tactic, compiler, or AI.

## Linear expected cost

For every n >= 2, the original initialized process satisfies

```text
(5*n-6)/36 <= E[T_n],
n/18 <= E[T_n] <= 1054*n,
E[T_n] = Theta(n).
```

The lower bound counts initial failures; one update can remove at most three.
The upper bound uses permanent barriers and

```text
V = 1000*(n-F) + 35*d + 2*r + 33*[r>0].
```

Its drift uses a proved conditional completion law of unretained coordinates
through observation histories, including rollback. It is not raw pointwise
unit drift for every fixed full suffix. See [the core report](REPORT.md),
[LinearPotential.lean](formal/mt/tightness/LinearPotential.lean), and
[LinearAsymptotics.lean](formal/mt/tightness/LinearAsymptotics.lean).
The current lower-bound proof retains its use of earlier quadratic finiteness.

For the canonical variable-dependency path, endpoint bad-event marginals are
1/6 and interior marginals are 5/12. Exact Shearer-polynomial calculations put
n=2,3 inside the region, n=4 on its boundary, and n>=5 outside. This is a
separate paper comparison, not a Lean/Nanoda theorem in this package. Outside
membership does not rule out every stronger MT theorem or establish novelty.

## Restricted certificate classes

For the SAME uniform kernel and initialization, a certificate requires V>=0
and expected drop at least delta>0 at every active full state, averaging only
the fresh redraw. Its budget is E_initial[V]/delta. The active-state score is
restricted, with V reset globally to zero on Good states:

```text
Coordinate-separable: c + sum_j f_j(X_j) + sum_i g_i(R_i).
One bridge per term: c + sum_i h_i(X_i,X_(i+1),R_i).
```

Both classes have explicit certificates for every n>=2. The constructed upper
budget is 3*9^(n-2)+1. Every coordinate-separable certificate, for n>=4, has
budget at least `(5^(floor((n-4)/2)+1)-3)/36`. Every one-bridge certificate,
for n>=10, has budget at least n^2/1248. Quadratic attainment for the larger
class is open. These do not restrict arbitrary nonseparable drift potentials.

Start with [certificate-existence/README.md](research/certificate-existence/README.md).
The [literature note](research/certificate-existence/LITERATURE.md) gives the
scoped comparison with drift analysis and HLS Theorem 1.6, and three concrete
questions for an independent reviewer. The HLS exclusion is paper-only.

The [window-locality study](research/window-locality/README.md) continues this
hierarchy by allowing each summand to read two adjacent bridges jointly.
Seven finite optimum certificates have independent exact primal/dual checks.
For n>=8, a written gauge/flux argument gives the width-two lower budget
`floor((n-6)^2/4)/20736`. Its local 91-row identity is checked over all 432
raw table columns, but the all-n argument is not a Lean/Nanoda theorem.
No matching quadratic upper bound is established. This study is retained
beside certificate-existence; it is a mathematical result with a different
verification status, rather than background material.

## Biased and history-dependent laws

The separate [biased study](research/biased-resampling/README.md) keeps the
same states and footprint but redraws thresholds from
`((1-p)/2,(1-p)/2,p)` and labels uniformly. The raw potential 6M+4W has unit
drift for every failed target when p is in [2/3,1]. M counts nonmaximal
internal thresholds and W counts weak labels.

For static p=2/3 and least-failed selection:

- Matching biased product initialization: n/24 <= E[T] <= 3n-2, and IsTheta.
- Original uniform initialization: E[T] <= 5n-4.

For any permitted history-dependent choice of a failed target and p in
[2/3,1], fresh draws obeying the selected product law give E[T]<=10n-6
from any fixed state/history. Initialized upper bounds are 5n-4 and 3n-2
for the respective original and biased starts. The full policy class has
upper bounds only; no all-policy Theta(n) statement is claimed.
The uniform-law certificate lower bounds do not transfer to this new law.

## Negative findings

- [Crew applicability gate](experiments/crew-mt-applicability/REPORT.md):
  STOP_UNKNOWN. Native stochastic retries exist, but the gate did not establish
  an MT correspondence. It stopped without a demonstrator. This is not an
  impossibility theorem.
- [Barrier-guided bias](experiments/barrier-guided-bias/README.md): the fixed
  policy p=1 at the barrier boundary, p=0 further away loses to static p=1
  for every n=2,...,5 under the same uniform initialization. Exact Bellman
  certificates support the comparison. No global static optimizer or
  impossibility result for all barrier policies is asserted.

## Build and checks

Lean: `leanprover/lean4:v4.35.0`.
Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The three mathematical workspaces depend on Mathlib and on this local core;
no PPGraph library or earlier project checkout is required.

```sh
lake exe cache get
make check
```

`make check` builds the core and both Lean research studies with warnings
treated as errors, checks source/provenance identities, verifies all seven
stored window optima and their local identity, and checks the stored
barrier-policy certificates. It does not overwrite sealed receipts, rerun
Crew, or run a fresh Nanoda replay. Individual targets are `core`,
`certificates`, `windows`, `biased`, `provenance`, and `barrier`.

The allowed audited axioms are propext, Classical.choice, and Quot.sound.
See [TOOLING.md](TOOLING.md) for independent-checker versions and fresh replay.
The root and certificate-study Nanoda checks cover selected roots and their
actual proof closures, not every assertion in every supplied module. The
biased study has Lean/audit evidence only. Kernel acceptance, correspondence
to an external implementation, and scientific priority are separate questions.

## Repository scope and provenance

`formal/` contains the core, tightness proof, earlier paper supplement, and
independent-audit support. `research/` contains certificate-existence,
window-locality, and biased-resampling. `experiments/` contains only the two negative findings.
`scripts/`, `tooling/`, `provenance/`, and relevant `evidence/` preserve source
identity, required historical inputs, and verification evidence.

The exact extraction manifest and module-migration record are unchanged.
Archived pre-migration bytes are required by the source validators. Audit
history is retained because current receipts refer to it. Build caches and
raw proof exports are ignored by Git; historical saved-evidence checks may
need those local artifacts or a fresh replay on another machine.

Unrelated framework copies, LUCES studies, and unfinished review drafts were
archived outside the repository during cleanup. Window-locality was initially
archived too, then restored byte-for-byte before the cleanup commit. Nothing
was mathematically invalidated or discarded. The cleanup record under
[provenance/cleanup-2026-11-06/](provenance/cleanup-2026-11-06/) identifies
archived paths and hashes. Crew's historical framework references resolve
through that record; its original protocol and receipt were not rewritten.

This project does not establish a practical PPG advantage, a new general
repair algorithm, arbitrary adaptive-AI guarantees, or a first formalization
of MT. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for source provenance.
