# Window-local potential budget study

This specification precedes the first optimization run. The target is the
smallest initial budget, not feasibility: an explicit separable certificate
already embeds into every window width r >= 1.

## Object and class

Use exactly the standalone MT chain: endpoints X_0=2 and X_n=0; interior
thresholds uniform in {0,1,2}; labels uniform in {0,1,2,3}; label1 is weak
(passes on equality), the other labels are strong (passes on descending or
equal thresholds). Select the least failed bridge and redraw its mutable
thresholds and own label. The law is the original 36 draws, retaining ignored
endpoint draws with multiplicity. Initial coordinates are independent.

For 1 <= r <= n, let Y_i=(X_i,X_(i+1),R_i), zero-based. Define

```text
score_n(s) = c_n + sum_(i=0..n-r) h_(n,i)(Y_i,...,Y_(i+r-1))
V_n(s) = 0 if Good(s), else score_n(s).
```

Each h is an arbitrary joint real table, with position and n dependence.
Only V as a whole must be nonnegative. Individual terms and the ungated
score on Good states need not be nonnegative. Overlapping thresholds in a
window are the same variables, not independent copies.

Normalize delta=1. For every active full state s require

```text
V_n(s) - (1/36)*sum_u V_n(replace(s,firstFailure(s),u)) >= 1.
```

The objective is E_initial[V_n]. No state/history/completion averaging is
allowed in a constraint. The global Good reset remains part of the class;
window width describes summand interactions, not total evaluation memory.

## Initial finite study

Primary width r=2, lengths n=3,4,5,6 in that order. Width1 at n=3,4 is a
comparison; width n at n=3 is a full-state calibration. Additional lengths
are permitted only after these results have exact certificates or an explicit
resource/verification failure. Do not infer all-length growth from this table.

Strong labels may be quotiented into a single class only with an explicit
symmetrization argument preserving locality, objective and every raw-state
drift constraint. A profile state then has initial integer mass 3^(number of
strong labels) over 3^(n-1)*4^n. Redraw weak/strong probabilities are 1/4
and 3/4, a multiplicity ratio 1:3, never uniform over the two classes.
The original four-label law remains the mathematical target.

## Certification

Numerical LP output is a candidate, not a result. Reconstruct rational primal
and dual vectors and independently verify all inequalities and weak duality
with exact arithmetic. Equal certified objectives establish a finite optimum;
unequal certified values establish an interval only. Numerical failure or
timeout is UNKNOWN, never infeasibility or a lower bound.

Validate the generated kernel against all36 original redraws. Check terminal
zero, product normalization, endpoint multiplicities and complete enumeration.
Record source hashes, solver versions, commands, timings and exact fractions.
An independently implemented verifier must not trust a solver success flag.

## All-length target and stopping interpretation

After the finite study, seek either a family in width2 with budget <=C*n for
one constant C independent of n, or a proved superlinear lower bound for all
width2 certificates. If neither is obtained, report the exact finite results
and the unresolved mathematical step. No extrapolation is an all-n theorem.

The broader fixed-width question quantifies one r, one C, and one threshold N
before all n>=max(N,r). Negating it alone does not determine how quickly a
necessary varying width r(n) grows. Existing Lean/Nanoda results and sealed
research evidence are unchanged. This study makes no novelty or speedup claim.
