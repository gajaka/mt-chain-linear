# Exact strong-label reduction for window-local certificates

This is a finite mathematical argument about the registered chain. It is not
a new Lean or Nanoda theorem. It justifies using weak/strong profile states in
the finite LP without restricting the attainable certificate budgets.

## The class being preserved

Fix n >= 2 and 1 <= r <= n. A raw state has interior thresholds in {0,1,2},
fixed endpoints X_0=2 and X_n=0, and labels R_i in {0,1,2,3}. Label 1 is weak;
labels 0, 2 and 3 are strong. Let

```text
score(s) = c + sum_(i=0..n-r) h_i(Y_i,...,Y_(i+r-1))
Y_i = (X_i,X_(i+1),R_i)
V(s) = 0 on Good, and score(s) otherwise.
```

Every table is arbitrary and position dependent. Only the complete V must be
nonnegative. The score is not constrained on Good, and individual summands
need not be nonnegative. Shared thresholds in overlapping Y_i are the same
coordinate. Write P for the original least-failed transition kernel, with
all 36 equiprobable redraws, and pi_0 for the original product initial law.

## Symmetries of the original process

Let G be the product, over label sites, of all permutations of {0,2,3}, each
extended to fix 1. An element g acts on a state by permuting its label at
each site independently, and leaves every threshold unchanged.

The pass table depends on a label only through whether it equals 1. Hence
Good(g.s)=Good(s), and the least-failed index is unchanged. For a fixed
selected site i, the concrete replacements obey

```text
g.replace(s,i,(a,b,t)) = replace(g.s,i,(a,b,g_i(t))).
```

The map (a,b,t) -> (a,b,g_i(t)) is a bijection on the 36 original redraws.
This identity includes endpoints: ignored threshold draws are still present
on both sides. It follows that

```text
P(f composed with g)(s) = (P f)(g.s).
```

The initial law is also invariant under every g, because its raw label
coordinates are uniform and independent. These facts use the original label
law; they would need rechecking for a different or adaptive redraw law.

## Averaging preserves every certificate obligation

Define A f(s) as the average of f(g.s) over all g in G. The identities above
give P A f = A P f. If V is nonnegative, vanishes on Good, and satisfies

```text
V(s) - (P V)(s) >= 1 for every active raw state s,
```

then A V has the same properties. In particular, for each active s,

```text
A V(s) - P A V(s)
  = average_g [V(g.s) - (P V)(g.s)] >= 1.
```

Its initial budget is identical: E_pi_0[A V] = E_pi_0[V].

Averaging does not enlarge a window. In A score, a summand h_i is averaged
only over the label sites already in its window; permutations at other sites
factor out. The resulting summand depends on the same r+1 thresholds and on
the weak/strong classes of its r labels. Since Good is invariant,
A V is the stopped version of this averaged score.

The G-orbits are exactly the profile fibers: identical thresholds and
identical weak/strong classes at every site. Thus A V factors through a
profile state and belongs to the stated profile window class.

Conversely, every profile certificate lifts to a raw certificate of the same
window width and budget. Therefore the sets of achievable budgets in the
raw and profile classes coincide. In particular their infima coincide; this
statement does not assume an optimizer has returned a minimum.

## Exact profile weights

A profile with k strong labels represents 3^k raw states. Its initial mass is

```text
3^k / (3^(n-1) * 4^n).
```

Summing these masses gives one, because the numerator sum over all profiles
is 3^(n-1)*(3+1)^n. Uniform mass over profile states is incorrect.

There are 18 profile redraw codes (a,b,weak), but they are not equiprobable.
For each threshold pair (a,b), the weak code has weight 1/36 and the strong
code has weight 3/36. The profile label marginal is therefore 1/4 weak and
3/4 strong. Endpoint dummy draws retain their original multiplicities.

For a lifted profile function, every raw state in a fiber has the same
current value and the same weighted successor-profile distribution. Checking
one profile row consequently checks the raw pointwise inequality for every
raw state in that fiber. This is an exact symmetry argument; it does not
replace a pointwise constraint by a completion or history average.

## Verification boundary

The independent checker should regenerate successor values using all 36 raw
redraws, weight initial profiles by their actual fiber sizes, and check the
full original feature space. Solver success flags, rounded coefficients,
sampled states, and a dual identity on only a reduced column basis are not
certificates. This reduction does not establish any all-length growth rate
for the minimum budget and makes no claim of scientific novelty.
