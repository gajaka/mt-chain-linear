# Scope of the comparison with drift and MT literature

This note separates known drift transfer theorems from the results
proved in this repository. It is not an exhaustive priority search. A failed
criterion or the absence of a matching statement in these references does not
establish scientific novelty.

## Additive drift does not mean a separable potential

Lengler's [Drift Analysis, arXiv:1712.00964v2](https://arxiv.org/abs/1712.00964)
is the author version of the chapter published in *Theory of Evolutionary
Computation* (2020). In [Section 3.1, Theorem 1](https://arxiv.org/html/1712.00964),
a nonnegative finite-state potential with uniformly positive conditional drift
yields `E[T] <= E[X_0]/delta`. Section 5 discusses finding the potential and
the canonical expected-remaining-time choice. The survey explicitly separates
selecting a potential from transferring drift information into a hitting-time
bound.

Here "additive" describes the drift condition. It does not require a sum of
coordinate functions. Therefore our obstruction is not an impossibility theorem
for additive drift analysis as a whole. It restricts the shape of the potential
and requires drift separately at every active full state. Variable or
multiplicative drift formulations and nonseparable potentials are not excluded
by the displayed theorem. A change of potential that leaves the defined class
is outside its conclusion.

Historical reference:
[He and Yao, Drift analysis and average time complexity of evolutionary
algorithms, Artificial Intelligence 127 (2001), 57-85](https://doi.org/10.1016/S0004-3702(01)00058-3).
The modern theorem displayed by Lengler is attributed there to He-Yao 2004,
with earlier foundations also discussed. The formulation used for comparison
here is Lengler's explicitly stated theorem.

The question for comparison is a class-wide obstruction for this specific MT
process, not whether positive-drift arguments or bad choices of potential were
already known.

## What HLS Theorem 1.6 actually tests

Primary source:
[He, Li and Sun, Moser-Tardos Algorithm: Beyond Shearer's Bound,
arXiv:2111.06527v1](https://arxiv.org/pdf/2111.06527v1), Theorem 1.6,
printed page 5 and its restatement on page 15.

For a matching M in the dependency graph, let delta_ij be positive lower
bounds on the corresponding event intersections. HLS subtracts
`delta_ij^2/17` from each matched event's marginal, giving a vector p_minus;
unmatched coordinates are unchanged. Its sufficient condition is that
`(1+epsilon)*p_minus` lies in the Shearer region for some epsilon > 0,
and its resulting expected resampling bound is `m/epsilon` for m events.
There is no nonchordal hypothesis in this criterion. A uniform linear
all-length bound would require uniform positive slack.

## A scoped exclusion of that criterion

**Status: paper argument with exact-rational arithmetic, not one of the
Lean/Nanoda results in this package.** The argument applies to Theorem 1.6
with the original events and canonical variable-dependency graph, for n >= 5.

The graph is a path: event i reads the mutable portion of
`{X_i, X_(i+1), R_i}`. For n >= 5, zero-based interior events 1, 2 and 3
form an induced three-vertex path, each with bad-event marginal 5/12.
The definitions are in [Chain.lean](../../formal/mt/core/Chain.lean), and
`initial_failure_probability` in
[InitialBadMoment.lean](../../formal/mt/tightness/InitialBadMoment.lean)
establishes that marginal.

For any permitted matching and any permitted intersection lower bound,

```text
delta_ij <= P(A_i intersect A_j) <= P(A_i) = 5/12

p_minus_i >= 5/12 - (5/12)^2/17 = 995/2448 = a.
```

On the induced path the empty-set Shearer polynomial is

```text
Q(x,y,z) = 1 - x - y - z + x*z.
Q(a,a,a) = 1 - 3*a + a*a = -324551/5992704 < 0.
```

On `[a,1]^3`, Q is nonincreasing in every coordinate: its derivatives are
`z-1`, `-1`, `x-1`. Thus the unscaled reduced vector already violates induced
Shearer positivity. Positive multiplicative slack cannot repair this: if a
scaled coordinate reaches 1, strict singleton positivity fails; otherwise
the same induced-path inequality applies.

This induced-subgraph test is also consistent with the global `q_I` definition
of the region. Summing `q_I(G,p)` over independent I contained outside the
three-vertex set S gives `Q_empty(G[S],p_S)`. If all global `q_I` were positive,
that sum would be positive, contradicting the calculation above.

The rational arithmetic is reproducible without floating point:

```python
from fractions import Fraction
p = Fraction(5, 12)
a = p - p*p/17
assert a == Fraction(995, 2448)
assert 1 - 3*a + a*a == Fraction(-324551, 5992704)
```

This excludes that sufficient criterion for n >= 5, including any matching it
permits. It does not address n = 2,3,4, alternative event encodings, stronger
criteria or all results in the HLS paper. It does not infer nonconvergence,
slow execution, or necessity of the present proof method.

## Questions for independent review

1. Does another existing theorem imply an O(n) expected resampling bound for
   these exact events, product initialization, least-failed scheduler and
   local redraw law? Please give the hypothesis mapping and uniform constants.
2. Is the exponential budget obstruction for all nonnegative, stopped
   coordinate-separable, raw pointwise-drift certificates already covered by
   a known result? Does that result cover this Good gate and this MT process?
3. Is there a known construction attaining O(n^2) budget in the larger
   one-bridge-per-summand class, or a stronger obstruction for that class?

The paired result to assess is constructive class existence plus its
exponential budget lower bound, alongside the linear cost of the same process.
The questions concern the mathematics and prior art separately from the
independent proof checking. No answer is presumed.
