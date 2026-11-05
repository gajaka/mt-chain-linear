# Explicit construction and a local algebraic obstruction

These notes complement the full finite LP in ../SPEC.md. They do not infer an
all-length growth rate from finite optima. The min-plus gauge and the all-length
budget argument are developed separately in GAUGE_AND_FLUX.md.

## An all-length upper bound already exists

For every n >= 2, CertificateConstruction.lean in the sibling
certificate-existence study constructs a stopped coordinate-separable
certificate with unit pointwise drift and initial budget at most

```text
3 * 9^(n-2) + 1.
```

Consequently the width-2 class is inhabited for every n >= 2. The exact
embedding needs no new probabilistic argument. Write its separable score as
c + sum_i e_i(Y_i), where

```text
e_i(a,b,r) = (if i=0 then 0 else f_i(a)) + g_i(r).
```

There are n-1 width-2 summands, starting at k=0,...,n-2. For k < n-2 use
h_k(Y_k,Y_(k+1)) = e_k(Y_k). In the final summand use
h_(n-2)(Y_(n-2),Y_(n-1)) = e_(n-2)(Y_(n-2)) + e_(n-1)(Y_(n-1)).
This is an exact raw-score identity, so the stopped score, every drift
constraint and the initial budget are identical. It establishes an explicit
exponential upper bound, not a quadratic or linear upper bound.

## A supplementary gate with one common width-2 table

A particularly simple candidate would use the same bounded table H at every
position. The supplementary gate tested exactly this homogeneous bulk case.
It did not restrict H to be nonnegative or additive.

Take six thresholds x_0,...,x_5 and five label profiles r_0,...,r_4. A profile
is weak or strong; strong means the original raw labels 0,2,3, each with its
original probability. Require

```text
bridge(x_0,x_1,r_0) passes,
bridge(x_1,x_2,r_1) passes,
bridge(x_2,x_3,r_2) fails.
```

The last two bridges have arbitrary outcomes. These are genuine admissible
least-failed stencils: precede x_0 by thresholds 2 and strong labels. Redraw
x_2, x_3 and r_2 using the original 36 equally likely draws. Exactly four
width-2 summands can change, with starts i-2,i-1,i,i+1. Their raw drift is
linear in four arbitrary width-2 tables.

The numerical feasibility problem had 3,024 admissible stencil rows and 108
profile-table variables. HiGHS reported infeasibility. That report is only
candidate evidence; the exact certificate below supplies the result.

## Exact certificate, including original raw labels

homogeneous-width2/DUAL_EXACT.json contains 91 strictly positive rational
weights on admissible stencils. They sum exactly to 1. Let C_0,...,C_3 be the
four weighted drift functionals, in order of summand position. The verified
identity is

```text
C_0(H) + C_1(H) + C_2(H) + C_3(H) = 0
```

for every original raw width-2 table H(a,b,c,l,r), with 432 entries.

verify_raw_dual.py independently rebuilds the original 36-draw operation. It
does not read the saved sparse drift rows or trust a solver status. It checks
all selected stencils against the original pass predicate, averages each old
strong label independently over 0,2,3, and checks all 432 coefficients. This
also verifies the label-profile lifting, including shared threshold and label
coordinates in overlapping windows. RAW_VERIFICATION.json records PASS.

It follows that no homogeneous table can have strictly positive uniform raw
drift on all those stencils: averaging such inequalities would yield delta <= 0
for delta > 0. The argument needs neither nonnegative H nor a budget premise.

For the actual stopped chain, the same contradiction is available when n >= 8:
choose a selected index 3 <= i <= n-5, put the stencil at positions i-2,...,i+3,
and pin the remote last bridge to X_(n-1)=1 with a weak label. It stays failed
under all draws of bridge i. Thus the Good reset never contributes to these
rows. This last realization argument is mathematical, not separately Lean
formalized here.

## What the exact identity also gives for indexed tables

For arbitrary position-dependent tables h_j, a full certificate implies on
each realizable remote bulk stencil

```text
delta <= C_0(h_(i-2)) + C_1(h_(i-1)) + C_2(h_i) + C_3(h_(i+1)).
```

Define a flux

```text
F_i = C_0(h_(i-2))
    + (C_0+C_1)(h_(i-1))
    + (C_0+C_1+C_2)(h_i).
```

The coefficient identity gives exactly delta <= F_i - F_(i+1). This is a
constraint on the full indexed class, rather than a conclusion that indexed
tables are impossible. Turning it into a budget lower bound additionally
requires a sound finite-state min-plus gauge, control of the initial mean on
the remote cylinder, and a count of usable bulk indices. Those obligations
are separate from the finite exact dual check; see GAUGE_AND_FLUX.md.

## Reproduction and boundaries

The generation and rational reconstruction scripts are preserved alongside
their copied original output and hash manifest in homogeneous-width2/.
The saved exact weights have denominators up to 26 decimal digits. This is an
exact rational certificate, not a claim of a minimal support or elegant dual.
The original solver timings were not separately recorded. The independent
raw validator records its own elapsed time.

This gate is not the full finite minimum-budget LP. In particular, failure of
a homogeneous table alone does not exclude a bounded-budget family of indexed
width-2 tables. No kernel formalization, novelty, or practical speedup is
claimed for the supplementary gate.
