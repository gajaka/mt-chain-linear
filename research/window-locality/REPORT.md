# Width-two locality study: results and evidence

## Outcome and status

The finite study is complete for its specified cases. Seven exact optimum
certificates passed the independent standard-library verifier: four primary
width-2 cases (n=3,4,5,6), two width-1 comparisons (n=3,4), and one full-width
calibration (n=3). One earlier n=6 numerical timeout is retained as UNKNOWN.

An additional exact local obstruction yielded an all-n paper lower bound:

```text
E_initial[V]/delta >= floor((n-6)^2/4)/20736, for n >= 8,
```

for every globally nonnegative stopped width-2 potential with raw pointwise
drift at least delta. It excludes an O(n) budget in that class, including
arbitrary position-dependent tables. This all-n argument is independently
reviewed but not Lean/Nanoda-checked. Its finite algebraic identity has an
independent exact checker. These are deliberately different evidence levels.

## Exact finite optimum values

Width 2:

```text
n=3:
139689479 / 124678400

n=4:
15425517587168481173967715723353404423 /
5976797796263367946229369478844593600

n=5:
155367060233583448184219143564144484220700809533521417807 /
26939499482212480441975457570373731557889404604676817056

n=6:
1069293186471649151320679784014693851417756928394450496141499 /
89400998153917406831861650387552366631758678723234180392576
```

Comparisons: width 1 at n=3 is `211081/172480`; width 1 at n=4 is
`3349223626493/980297624096`. The full-width n=3 calibration is `12517/11424`.

| Case | Profile states | Feature columns | Inequalities | Positive dual rows |
| --- | ---: | ---: | ---: | ---: |
| n=3, r=1 | 72 | 31 | 108 | 23 |
| n=3, r=2 | 72 | 73 | 108 | 45 |
| n=3, r=3 | 72 | 73 | 108 | 54 |
| n=4, r=1 | 432 | 49 | 752 | 39 |
| n=4, r=2 | 432 | 181 | 752 | 139 |
| n=5, r=2 | 2,592 | 289 | 4,864 | 234 |
| n=6, r=2 | 15,552 | 397 | 30,240 | 324 |

There is one drift and one nonnegativity inequality per active profile state.
Good-state feature rows are zero, including the offset column. Every feature
coefficient is a free real variable; there are no nonnegative-table or
translation-invariance restrictions in these LPs. Boundary windows use fixed
endpoint values, and overlapping coordinates refer to the same state entries.

## What an exact optimum certificate proves

The numerical LP is `min c*x`, `A*x >= b`, with unrestricted x. Its diagnostic
output selects basic columns and tight rows. The generator solves that square
system over rational numbers, then reconstructs a dual vector. It checks

```text
A*x >= b,     y >= 0,     A^T*y = c,     c*x = b*y.
```

All original feature columns are included in the final equality despite
linear dependencies between overlapping-window features. An exactly zero
gap proves a finite optimum; a solver success flag alone proves nothing.

The independent checker imports neither the optimizer nor its matrix. It
rebuilds the full variable inventory, Good gate, initial probabilities,
least-failed choices and all 36 original redraws. It verifies every active
profile's drift, not an averaged constraint over profiles. It also checks
the exact initial failure moment `(5*n-6)/12` and normalization of raw state
masses. The n=6 run covers 995,328 raw states by exact profile symmetry and
15,552 profile representatives; the enumeration does not silently treat
weak and strong labels as equally likely.

The [profile symmetry proof](theory/PROFILE_SYMMETRY.md) explains why the
profile optimum equals the unrestricted four-label optimum. Averaging any
raw certificate over independent strong-label permutations preserves window
width, nonnegativity, all pointwise constraints and the objective; a profile
certificate lifts conversely. The independent checker enumerates all 36
raw redraws at every active profile.

Negative controls for a zero primal, zero dual and missing feature coordinate
were all rejected. A separate local-dual check rejects zero mixture weights,
a changed functional and a stencil whose selected bridge no longer fails.

## The all-length argument

[GAUGE_AND_FLUX.md](theory/GAUGE_AND_FLUX.md) contains the complete paper
derivation, including the n=8 endpoint case and arbitrary raw 432-entry
tables. [CONSTRUCTION_NOTES.md](theory/CONSTRUCTION_NOTES.md) gives the
explicit exponential upper embedding and how the finite identity was found.

The local witness consists of 91 positive rational weights on admissible
stencils; their weights sum to one. The independent raw checker reconstructs
four drift functionals, verifies their coefficientwise sum is zero and checks
the `1,2,1` cumulative coefficient bounds used in the argument. It does not
trust the saved sparse rows. The remaining all-n steps are finite min-plus
gauging, realizing each stencil as a true least-failed state with a surviving
remote failure, pairing a sequence of spatial flux values, and comparing
conditional product means. These have internal independent mathematical
review, but no new Lean theorem is claimed.

The homogeneous-table infeasibility check alone would not exclude indexed
tables. It is the subsequent flux argument that handles the unrestricted
position-dependent class. Likewise, the finite minimum-budget table is not
used as evidence of asymptotic growth in that proof.

## Resource failure and retry

`n6-r2-attempt-001` reached its 180-second simplex limit. Its reported
unfinished objective, about 8.746, is not presented as a valid bound. That
attempt remains UNKNOWN and has no certificate.

For `n6-r2-attempt-002`, the same mathematical matrix was passed to HiGHS
interior point with crossover. Numerical optimization took about 1.023 s;
matrix generation, exact reconstruction and generator-side verification
together took about 3.362 s. The independent exact verifier took about 2.033 s.
These are tool measurements, not the resampling process complexity.

The v1 runner was archived byte-for-byte before adding `--solver`. Both
attempts record hashes and version information. Existing output directories
are never reused by the primary optimizer. The supplementary bulk-gate
generation was exploratory; its original discovery wall time was not recorded,
and the provenance document states that limitation explicitly.

## Boundaries and next obligation

The new paper argument says that two-bridge summands do not suffice for a
linear raw pointwise-drift budget. It does not say the best budget is exactly
quadratic: no matching O(n^2) construction is provided. An explicit
exponential upper bound is already available by embedding the established
separable construction, so this is not an empty-class argument.

The first open width after accepting the paper argument is three bridges.
Whether any fixed width suffices remains open. The next formal verification
obligation is to translate the width-2 gauge/flux argument and exact witness
into Lean before assigning it the same status as the older separations.

No old formal source, prior receipt or source-project file was modified.
No new Lean/Nanoda run was performed for this study, and no scientific-priority
or practical speedup claim is made. The immutable source-and-evidence manifest
and aggregate result are [MANIFEST.json](MANIFEST.json) and
[evidence/SUMMARY.json](evidence/SUMMARY.json).
