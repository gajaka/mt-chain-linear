# Width-two windows: an all-n gauge and flux argument

Status: paper argument, using the exact finite identity independently checked
by `homogeneous-width2/verify_raw_dual.py`. This document is not a Lean or
Nanoda certificate. The finite identity alone is not the all-n theorem; the
extension below also requires the gauge, realizability, and initial-measure
arguments.

## Claim and conventions

There are `n` bridges, indexed `0,...,n-1`. The thresholds satisfy `X_0=2`,
`X_n=0`; all other thresholds and all four-valued labels have the registered
independent uniform initial law. Put

    Y_j = (X_j, X_(j+1), R_j).

Allow arbitrary position-dependent real tables

    S(s) = c + sum_(j=0)^(n-2) h_j(Y_j,Y_(j+1)),
    V(s) = 0 if Good(s), and S(s) otherwise.

An adjacent pair is coherent: the second threshold of `Y_j` equals the first
threshold of `Y_(j+1)`. Thus a table has `3^3 * 4^2 = 432` possible entries,
not `36^2` independent entries. No sign condition is imposed on an individual
`h_j`; the hypotheses are only:

1. `V >= 0` on every original full state;
2. at every active full state, the registered least-failed full-footprint
   redraw satisfies `V(s) - E[V(next) | s] >= delta`, where `delta > 0`.

Let `B = E_initial[V] / delta`. The argument below gives, for `n >= 8`,

    B >= floor((n-6)^2 / 4) / 20736.

This excludes a uniform linear initial budget for this width-two additive
class. It does not exclude arbitrary functions of a small observable, general
nonadditive global potentials, or the completion-averaged certificate already
used for the actual linear expected runtime.

## 1. Preserve an active remote failure

Restrict to the cylinder

    E = { X_(n-1)=1 and R_(n-1)=1 }.

The final bridge is then `1 -> 0` with the weak label, so it fails regardless
of all remaining coordinates. Consequently every state in `E` is active,
`V=S` there, and `P_initial(E)=1/12`. Global nonnegativity therefore implies

    E_initial[V] >= (1/12) E_initial[S | E].

Interior updates considered below never change either pinned coordinate.
Both their starting states and every redraw successor stay active in `E`.
The stopped drift is therefore exactly the raw-score drift on those updates.

## 2. A finite min-plus gauge makes every window nonnegative

View the bridge observations as vertices of a finite layered directed graph.
An edge `u -> v` exists when `u.right = v.left`; its layer-`j` cost is
`h_j(u,v)`. Initially `u.left=2`. The final vertex is fixed to

    v_* = (1,0,1).

Every coherent vertex at layer 1 is reachable from an initial vertex: for a
target `(a,b,r)`, choose any initial label on `(2,a,label)`. By extending
backwards, every vertex at every later layer is also reachable. All minima
below are therefore minima of nonempty finite sets; no infinite values or
unattained infima are introduced.

Let `D_j(v)` be the minimum cost of a path with exactly `j` windows, ending
at vertex `v`. At layer zero define `D_0=0` only on the permitted initial
vertices. Then

    D_1(v) = min_(u.left=2, u.right=v.left) h_0(u,v),
    D_(j+1)(v) = min_(u.right=v.left) [D_j(u) + h_j(u,v)]  (j>=1).

Define new tables on all coherent pairs by

    q_0(u,v) = h_0(u,v) - D_1(v),                  if u.left=2;
    q_0(u,v) = 0,                                  otherwise;
    q_j(u,v) = h_j(u,v) + D_j(u) - D_(j+1)(v),     if j>=1.

The minimum inequalities imply `q_j >= 0` entrywise. The path sum telescopes:

    sum_j q_j(Y_j,Y_(j+1)) = sum_j h_j(Y_j,Y_(j+1)) - D_(n-1)(v_*).

Write `K = c + D_(n-1)(v_*)`. A minimizing path exists and is a genuine
original-chain state in `E`. Evaluating `S >= 0` at that state proves `K>=0`.
Hence, on every state in the remote cylinder,

    S(s) = K + sum_j q_j(Y_j,Y_(j+1)),   K>=0, q_j>=0.

This equality holds before and after each interior redraw. Their drift
inequalities transfer exactly to the gauged score. The first-window
unsupported entries set to zero never occur in these identities.

## 3. The finite dual applies at every bulk location

For each selected index `i` with

    3 <= i <= n-5,

the six thresholds `X_(i-2),...,X_(i+3)` and five labels
`R_(i-2),...,R_(i+2)` are freely assignable and are disjoint from the pinned
last bridge. Require the two bridges immediately preceding `i` to pass and
bridge `i` to fail. Every such local assignment extends to a state whose
least failure is exactly `i`: take a strong passing prefix from the fixed
left threshold 2 to the first local threshold, use the two prescribed
passing bridges, and keep the remote final failure. All labels called
strong in the finite identity may independently be any of `0,2,3`.

An update at `i` changes precisely the four score windows with starts

    i-2, i-1, i, i+1.

The saved rational dual is a positive mixture of 91 such local assignments,
with weights summing to one. The original four-label reconstruction averages
old strong labels independently and explicitly enumerates all 36 redraws.
It supplies linear functionals `C_0,C_1,C_2,C_3` on the 432-entry tables with

    C_0 + C_1 + C_2 + C_3 = 0   coefficientwise,

and for each bulk `i`, averaging the pointwise drift hypotheses yields

    delta <= C_0(q_(i-2)) + C_1(q_(i-1)) + C_2(q_i) + C_3(q_(i+1)).

The coefficients in each `C_a` are a difference of two probability mass
functions: the old window marginal and its redraw successor marginal,
averaged under the positive dual mixture. Thus each coefficient has
absolute value at most 1. This probability interpretation follows directly
from the reconstruction, rather than from a floating-point solver status.

## 4. A spatial flux must grow linearly

For `i=3,...,n-4`, define

    F_i = C_0(q_(i-2))
        + (C_0+C_1)(q_(i-1))
        + (C_0+C_1+C_2)(q_i).

The zero-sum identity gives, for `i=3,...,n-5`,

    F_i - F_(i+1) >= delta.

There are `m=n-6` flux values. For any decreasing sequence with successive
drops at least `delta`, pairing values symmetrically gives

    sum_i |F_i| >= delta * floor(m^2/4).

Indeed, the paired values at distance `d` differ by at least `delta*d`, so
their absolute values sum to at least that difference. For even `m=2a` the
distances sum to `a^2`; for odd `m=2a+1` they sum to `a(a+1)`.

Let `M_j` be the uniform mean of the 432 entries of nonnegative `q_j`.
Since each `C_a` coefficient has absolute value at most one,

    |C_a(q_j)| <= 432 M_j.

For the three cumulative functionals in `F`, the coefficient bounds are
`1,2,1`: the last one equals `-C_3`. Consequently

    |F_i| <= 432 M_(i-2) + 864 M_(i-1) + 432 M_i,
    sum_i |F_i| <= 1728 sum_(j=1)^(n-4) M_j.

Every `j` appearing here is an interior unpinned window. Conditional on `E`,
its three thresholds and two labels retain exactly the uniform product law,
so its conditional expected contribution is `M_j`. All other gauged terms
and `K` are nonnegative. Combining the inequalities gives

    E_initial[V]
      >= (1/12) sum_(j=1)^(n-4) M_j
      >= delta * floor((n-6)^2/4) / (12*1728).

Dividing by `delta` proves the displayed budget lower bound.

## Remaining verification work and limits

- The finite 432-column dual identity has an exact rational checker.
- The all-n min-plus, witness-extension, flux, and expectation arguments in
  this document are paper arguments awaiting a formal Lean implementation.
- Finite-n LP optima are separate evidence; they are not used as asymptotic
  extrapolation in this argument.
- The constant is deliberately coarse. No matching quadratic upper bound,
  optimal leading constant, width-three obstruction, general fixed-width
  theorem, or scientific-priority claim follows from this document.
- Existence in the class is already available by embedding the established
  coordinate-separable exponential-budget certificate. This lower bound is
  not based on assuming an otherwise possibly empty class.
