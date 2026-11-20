# Inhabited potential classes and an exponential obstruction

This study constructs drift certificates for two restricted potential classes
of the finite MT chain. Every coordinate-separable certificate requires an
exponential initial budget, although the expected resampling count of the same
initialized process is Theta(n). A larger class, with one bridge per summand,
has a quadratic budget lower bound.

The results below have Lean proofs and a recorded Nanoda check of nine selected
roots and their actual proof closure. They are results about the specified MT
chain, not a faster algorithm or a claim of scientific priority.

## Results

Write `budget(C) = E_initial[V_C] / delta_C` for the upper bound supplied by a
nonnegative potential with uniform pointwise drift at least `delta_C > 0`.
All expectations use the original independent product initialization.

```text
Coordinate-separable class:

  n >= 2: an explicit certificate C_n exists, with delta = 1.
          budget(C_n) <= 3*9^(n-2) + 1.

  n >= 4: EVERY certificate C in this class satisfies
          budget(C) >= (5^(floor((n-4)/2)+1) - 3) / 36.

Larger one-bridge-per-summand class:

  n >= 2: an explicit certificate exists by an exact embedding of C_n.
          It has the same budget as C_n.

  n >= 10: EVERY certificate C in this larger class satisfies
           budget(C) >= n^2/1248.

Actual expected resampling count, for the same initialized process:

  n >= 2: n/18 <= E[T_n] <= 1054*n.
```

Consequently, no quadratic-budget family exists in the coordinate-separable
class. Its all-length existence is constructive, and its class-wide lower
bound is exponential. The displayed upper and lower bounds
do not identify the optimal exponential base or leading constant. For the
larger class, quadratic attainment remains open; the exponential lower bound
for the narrower class does not transfer to it.

## Exactly which potentials are restricted

The project [README](../../README.md) specifies the process. This section uses
Lean's zero-based bridge index `i = 0,...,n-1` and threshold positions
`j = 0,...,n`, with fixed endpoints `X_0 = 2`, `X_n = 0`.

The coordinate-separable class has an active-state score

```text
score(s) = c + sum_(j=1..n-1) f_j(X_j) + sum_(i=0..n-1) g_i(R_i).

V(s) = 0         if every bridge passes (Good)
       score(s)  otherwise.
```

The terminal reset is part of the definition. Thus this is a
separable score on active states, with a global Good gate; it is not a claim
that V is coordinate-separable on the whole state space. The general class
does not require the ungated score to be nonnegative at Good states.

The larger class replaces the score by

```text
score(s) = c + sum_(i=0..n-1) h_i(X_i, X_(i+1), R_i),
```

with the same Good gate. The source namespace calls this `NeighborSeparation`.
Each summand reads the two thresholds and one label of ONE bridge. It does
not allow an arbitrary joint function of two full adjacent bridges.

In both classes the requirement is pointwise in the full raw state:

```text
V(s) >= 0                           for every state s
V(s) - (1/36)*sum_u V(replace(s,i,u)) >= delta
                                    whenever i is s's first failed bridge.
```

Only the fresh redraw is averaged in this condition. There is no averaging
over states, histories or completion fibers. The chain's observed-prefix
linear potential has a different drift obligation: it uses the proved
conditional completion law. These lower bounds do not apply to that proof.

## The explicit certificate

For `n >= 2`, define

```text
A_j = 9^(n-1-j),                       1 <= j <= n-1
f_j(a) = 0 if a = 2, else 3*A_j

t_i = 1                               if i = 0 or i = n-1
      6*A_(i+1)                       otherwise
g_i(r) = 4*t_i if r = 1, else 0

c = 0, delta = 1.
```

All components are nonnegative. Their centered threshold values are
`(A_j, A_j, -2*A_j)` and centered label values are `(-t_i,3*t_i,-t_i,-t_i)`.
For an internal repair, `A_i = 9*A_(i+1)` makes every failing local triple
have raw-score drift at least one. The two endpoint cases are proved
separately. Replacing a successor's nonnegative raw score by zero when it is
Good can only improve the drift. The raw initial mean is exactly
`3*9^(n-2)+1`; the stopped initial budget is at most that number.

This is an actual definition of `DriftCertificate n`, not an assumption that
such an object exists. The embedding into the larger class assigns each
mutable threshold cost once, to the bridge whose incoming threshold it is,
and preserves V, delta and budget exactly.

## Why the lower bound is exponential

The proof tests the drift requirement on selected internal failures with a
separate remote failure. That remote failure survives all 36 local redraws,
so the Good reset cannot conceal any of the local score inequalities.

Center a threshold table as `A_j = (a_j,b_j,c_j)`, with zero sum, and put
`v_j = (g_j(1) - mean(g_j))/3`. Averaging the three strong-label failure
inequalities, and using the weak-label failures, gives

```text
S_ab: A_j(a) + A_(j+1)(b) - v_j   >= delta    for a < b
W_ab: A_j(a) + A_(j+1)(b) + 3*v_j >= delta    for a != b.
```

Exact positive combinations give

```text
5*c_(j+1) - c_j   >= 8*delta
5*a_j - a_(j+1)   >= 8*delta
c_j + a_(j+1)    <= -8*delta/3.
```

At a middle position, the last inequality forces a negative component on
one side. The first two propagate it toward an endpoint with factor five
per step. For `2*k+4 <= n`, some threshold table therefore has oscillation
at least `delta*(5^(k+1)-3)`. The product-budget lemma converts
that oscillation into the budget lower bound with divisor 36.

This argument uses exact inequalities in Lean. Numerical searches are not
premises of the proof. Full statement and evidence details are in
[REPORT.md](REPORT.md).

## Sources and reproducibility

| Source | Role |
| --- | --- |
| [CertificateConstruction.lean](formal/CertificateConstruction.lean) | Explicit inhabitant, pointwise drift, upper budget |
| [ExponentialObstruction.lean](formal/ExponentialObstruction.lean) | Class-wide exponential lower bound |
| [NeighborEmbedding.lean](formal/NeighborEmbedding.lean) | Larger-class inhabitant and budget equality |
| [CertificateResults.lean](formal/CertificateResults.lean) | Nonvacuous separations and actual process bounds together |
| [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) | Identities of mathematical sources, reference snapshots and audit support |

Build the root package first, then run from this directory:

```sh
lake --wfail build CertificateStudy
python3 -B scripts/verify_sources.py
```

This is a separate Lake package using the project's pinned Lean 4.35.0 and
Mathlib revision. Its full local proof import closure is 49 modules:
18 research modules plus 31 modules from the root package. This proof closure
uses the concrete chain directly and is independent of the general theory
library.

The recorded strict build compiled all 18 research modules from an empty study
build directory, reusing root and external dependency caches: zero warnings
and zero errors. Nanoda verification checked 18,183 expanded declarations
from nine selected roots, with only `propext`, `Classical.choice`, `Quot.sound`.
This does not mean every theorem in all 49 modules was independently replayed.

See [evidence/VERIFICATION.json](evidence/VERIFICATION.json). With the recorded
external tools, raw export and local build artifacts present, saved verification
is read-only:

```sh
python3 -B scripts/independent.py --verify --attempt attempt-001
```

For a fresh replay, use a new unused attempt name and the pinned tools described
in [TOOLING.md](../../TOOLING.md). Raw exports and binaries are excluded from
Git. Recorded audit attempts and source reference snapshots are preserved.

## Research interpretation

The result separates the budget of a precisely restricted certificate class
from the actual cost of one process. It does not show that additive drift
analysis in general is weak: an arbitrary potential need not be separable.
It does not prove that completion averaging is necessary for every possible
linear proof, or that this chain is faster than another repair algorithm.

[LITERATURE.md](LITERATURE.md) distinguishes the established drift transfer
theorems from the present restriction on potential shape, and gives a scoped
HLS comparison. Scientific novelty remains a question for independent expert
review; formal checking establishes the stated mathematics, not priority.
