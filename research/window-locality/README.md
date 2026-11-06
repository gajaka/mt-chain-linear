# How much local interaction can certify linear resampling cost?

This study asks whether allowing two adjacent bridges per potential summand
can certify the linear expected cost of the MT chain. It obtains exact finite
minimum budgets and an all-length paper obstruction for that width. Two-bridge
interaction improves the small examples but still cannot give a uniform O(n)
budget under the paper argument.

**Verification status:** finite LP optima and the local algebraic witness have
independent exact rational checks. The all-n extension is a written argument
with independent internal review, not yet a Lean/Nanoda theorem.

## The exact question

For the original MT chain, write `Y_i=(X_i,X_(i+1),R_i)`. Width r permits

```text
V_n(s) = 0                                              if Good(s)
         c_n + sum_(i=0..n-r) h_(n,i)(Y_i,...,Y_(i+r-1)) otherwise.
```

The tables are arbitrary joint real functions and can depend on both n and
position. Only the whole V must be nonnegative. Require raw pointwise drift
at least one under the same least-failed 36-draw update and minimize

```text
B_r(n) = inf E_initial[V_n].
```

Initialization is the original product law. The test for an O(n) certificate
is one constant C with `B_r(n) <= C*n` for all sufficiently large n and fixed
r. This is a constraint on interactions inside each summand, not on total
evaluation memory. The global Good reset is explicitly retained.

[SPEC.md](SPEC.md) defines the finite optimization and all-length question.
The explicit coordinate-separable certificate embeds into width 2, establishing
feasibility. The objective here is its best possible initial budget.

## Finite results: exact primal and dual certificates

The decimals below are rounded presentations of exact rational optima. Every
reported optimum has a feasible rational primal, a nonnegative rational dual
matching every original feature column, and an exactly zero primal-dual gap.

| n | Width 1 optimum | Width 2 optimum | Width n calibration |
| --- | ---: | ---: | ---: |
| 3 | 1.223799861 | 1.120398393 | 1.095675770 |
| 4 | 3.416537533 | 2.580900026 | Not run |
| 5 | Not run | 5.767258606 | Not run |
| 6 | Not run | 11.960640357 | Not run |

At n=3 and n=4, width 2 strictly improves the optimum over width 1. That is
a statement about certificate budgets, not a faster resampling algorithm.
These four width-2 values alone establish no asymptotic growth rate.

The larger n=6 problem has 15,552 profile states, 397 feature variables and
30,240 inequalities. Its independent verifier checks every active profile
against all 36 original redraws: 544,320 redraw evaluations. The profile
reduction is exact for the entire optimum by
[strong-label symmetrization](theory/PROFILE_SYMMETRY.md), rather than an
unjustified restriction to label-invariant candidates.

Full fractions and certificate paths are in [REPORT.md](REPORT.md) and
[evidence/SUMMARY.json](evidence/SUMMARY.json).

## All-n paper result: width 2 still cannot give a linear budget

For every arbitrary position-dependent width-2 certificate with drift
`delta > 0`, the argument in [GAUGE_AND_FLUX.md](theory/GAUGE_AND_FLUX.md) gives

```text
n >= 8:

    E_initial[V] / delta >= floor((n-6)^2 / 4) / 20736.
```

Thus width 2 has an Omega(n^2) obstruction. The argument does not extrapolate
the finite optima, and it does not assume a shared table at every position.
It applies to all 432 entries of each original raw two-bridge table, including
different costs for the three strong labels.

Its steps are:

1. Keep the remote final bridge failing, an event of initial probability 1/12.
   It stays failed under every local update used in the argument, removing
   the global Good gate from these drift rows.
2. Apply a finite min-plus change of the window tables. The score on that
   cylinder is preserved, but the new terms and remaining offset are
   nonnegative. This is derived from global nonnegativity, not imposed as an
   extra hypothesis on the original table entries.
3. Use 91 positive rational weights on genuine least-failed local assignments.
   Their four window drift functionals cancel when summed coefficientwise.
   An independent checker reconstructs this identity for all 432 raw columns
   with the original 36 draws.
4. For position-dependent tables the same identity gives a spatial flux whose
   successive values differ by at least delta. Across n-6 positions its total
   absolute value is quadratic. Nonnegative table means convert that into the
   displayed initial-budget bound.

The finite coefficient identity is executable exact evidence. The min-plus
construction, witness extensions, sequence bound and expectation comparison
for arbitrary n remain paper proof obligations awaiting Lean formalization.
The exact witness alone must not be presented as a machine-checked all-n proof.

## Updated locality map

| Potential class | Available conclusion | Status |
| --- | --- | --- |
| Coordinate-separable active score | Exponential budget lower bound; explicit exponential upper certificate | Lean + Nanoda in [certificate-existence](../certificate-existence/README.md) |
| One bridge per summand | Omega(n^2); class inhabited | Lean + Nanoda in the same sibling study |
| Two adjacent bridges per summand | Omega(n^2); class inhabited | All-n paper argument + exact local identity; finite optima independently checked |
| Three adjacent bridges per summand | Linear budget possible or impossible? | Open |
| Arbitrary fixed width | Does any fixed width suffice? | Open |

Under the paper result, width 3 is the next open case in this hierarchy.
The fully formalized boundary remains the width-1 theorem until width 2 is
formalized. No quadratic upper attainment is established for width 1 or 2.
The actual expected resampling count remains Theta(n); this study does not
change the process, initialization or scheduler.

## Reproduce or check without a solver

The independent checker uses only the Python standard library:

```sh
python3 -B scripts/verify_certificate.py \
  evidence/n6-r2-attempt-002/CERTIFICATE.json

python3 -B theory/homogeneous-width2/verify_raw_dual.py \
  theory/homogeneous-width2/DUAL_EXACT.json
```

Run the second command without `-O` or `PYTHONOPTIMIZE`: its assertions are
part of the check. The recorded independent run explicitly enabled them.
Neither command needs the numerical solver or a Lean build. Use a new unused
path if saving a new verification receipt.

To generate another finite candidate, use a local virtual environment with
[requirements.txt](requirements.txt):

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python scripts/window_lp.py --n 6 --width 2 --solver ipm \
  --time-limit 300 --out evidence/n6-r2-local-001
```

The optimizer refuses to overwrite an existing output directory. Numerical
output proposes a basis; rational reconstruction and exact inequalities must
succeed before it reports an optimum, followed by the independent checker.
The first n=6 simplex run timed out and remains `UNKNOWN`. Its unfinished
objective is not a bound. A separate interior-point run completed and supplied
the independently checked certificate. Both runs used the same mathematical
model. [provenance/window_lp-v1.py](provenance/window_lp-v1.py) records the
runner version used for the first attempt.

The results concern certificate budgets for the specified resampling law.
They do not establish algorithmic speedup or a lower bound on unrestricted
drift methods. Scientific novelty remains open for independent review.
