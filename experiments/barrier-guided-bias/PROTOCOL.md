# Barrier-guided bias: bounded exact comparison

Written before computing the new policy's outcomes, 2026-11-06.

## Question and scope

Does one fixed barrier-position policy reduce expected redraw count compared
with the best constant threshold bias on the original chain, for n = 2, 3, 4, 5?
This is a finite computational experiment. It does not extend any Lean theorem.
The sealed biased-resampling study and its evidence are not changed.

## Fixed model

Use the original ChainState, bridgePass, firstFailure, replace, and barrierHeight
definitions. The endpoints are X_0 = 2 and X_n = 0. Each internal threshold is
in {0, 1, 2}. A weak label passes exactly when its thresholds are equal; each
of the other three labels passes when the right threshold is no greater than
the left. Always repair the least failed bridge. Redraw its mutable endpoint
thresholds independently and its own label uniformly among all four labels.
Unchanged endpoints and all other coordinates remain fixed.

Threshold law: mu_p(0) = mu_p(1) = (1-p)/2, mu_p(2) = p.
The static family is the complete interval 0 <= p <= 1.

All arms start with exactly the SAME original uniform product law: internal
thresholds uniform on three values and labels uniform on four values. Count
redraws only, excluding initialization. Good states stop at cost zero.

## Preselected adaptive policy

Let i be the ZERO-BASED index of the least failed bridge. Let F be exactly
barrierHeight: the largest j+1 such that the prefix through bridge j passes,
X_j = 2, and label j is strong; F = 0 when there is no such barrier.
For an active state F <= i. Set

- p = 1 if i = F (the repair is adjacent to the barrier boundary);
- p = 0 if i > F (the repair is further to the right).

This formula is fixed before its outcomes are known. It is intentionally a
small test of a barrier-dependent law, including laws outside p >= 2/3.
It will not be tuned, replaced, or supplemented after seeing the results.

## Computation and exact checks

The three strong labels may be lumped into one symbol of mass 3/4 and the weak
label into one symbol of mass 1/4. Check that the transition and barrier rules
respect this quotient; there are 3^(n-1) * 2^n quotient states.
Use exact rational transition probabilities and uniform-start weights.
Check for reachable nonabsorbing recurrent classes, especially at p = 0 or 1.
If one exists, report infinite mean rather than a numerical solver failure.
For finite cases retain rational Bellman solutions and independently check
h(s) = 1 + sum_t K(s,t)h(t) on every active state, h = 0 on Good states,
nonnegativity, absorption reachability, and the exact initialized average.

Compare static p = 1/3 (the original uniform law), p = 2/3 (the sealed biased
study), and p = 1, at minimum. A grid or numerical search may locate additional
static candidates but cannot certify the global best over [0,1]. Any claim of
an attained global minimum needs a separate exact argument. If ANY one valid
static p is no worse than the adaptive policy, this already proves that the
adaptive policy fails to beat the best static law; locating that best law is
then unnecessary for the negative conclusion. Explicitly distinguish these
two statements in the report.

The old /tmp/mtcheck/exact.py uses floating-point value iteration and a matching
initialization. Its numbers are cross-checks only, not rational certificates
and not the common-initialization specification of this experiment.

## Decision and stopping rule

Report every n, including unfavorable or inconclusive results. No small-n
trend establishes an all-n result or a running-time advantage. A positive
comparison with only tested static candidates is inconclusive about the best
static law. Failure of this one policy does not exclude all barrier policies.

Stop after n <= 5, or after 30 minutes of solver work if exact computation
cannot be completed. Preserve partial outcomes and explain any unresolved
case. No n = 6, policy tuning, new benchmark, formalization, commit, or push is
part of this experiment. More Lean work is warranted only after a clearly
stated positive computational result and a further user instruction.
