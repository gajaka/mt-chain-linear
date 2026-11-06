# Formalization report

The mathematical statements and their scope are documented in [README.md](README.md).
The latest replay status is in [RESULT.json](RESULT.json); attempts and logs
are preserved under `.build/`. A PASS is to be read only from an actual
completed replay, not from this report's prose.

## Guarantee ledger

| Change | Prior guarantee | New obligation | Formal status |
|---|---|---|---|
| Uniform law to `(1/6,1/6,2/3)` | Original initialized least-failed Theta(n), unchanged | Fresh normalization, original-footprint binding, new raw drift and new initial moments | Separate theorems in this study |
| Fixed bias to history-dependent bias | New static pointwise drift | Parameter stays in `[2/3,1]`; every selected target is failed; fresh conditional product law | Explicit full-state-history recurrence and uniform upper bound |
| Finite horizon to infinite expected cost | Finite weighted sums | Supremum bound without presupposing termination | `adaptiveTotalWork_le_potential` and finiteness theorem |
| Counting lower bound | At most three affected certificates per `replace` | New initialization first moment; vanishing remainder justified by new upper bound | Static refined lower bound and `IsTheta` |

The adaptive theorem does not apply a fixed-product MT convergence
theorem. It proves a common conditional drift directly. The static law is a
full-footprint product-resampling instance. The uniform kernel and its
potential-class separations concern a different redraw law.

## Verification interpretation

`BiasedAudit` checks every theorem in the study namespace, including generated
equation and constructor theorems, through actual checked kernel constants.
The inventory count therefore is not a count of independent mathematical
results. The raw closure includes theorem bodies, inductive bundles and
recursor rules; it does not consult the cached `collectAxioms` result.
The audit also compiles independently spelled versions of the main targets
and a concrete inhabitant of the policy class. This checks assumptions and
avoids treating a theorem over an uninhabited controller class as evidence.

Four deliberately invalid controls must be rejected: an out-of-range bias,
the false uniform unit-drift assertion, removal of the tactic score, and a
new transitive axiom injected into a copied study theorem. Original/live
sources are not mutated by these controls.

This is Lean kernel verification plus a raw proof-dependency audit. It is
not a new second-kernel check or a timing benchmark. Scientific novelty
remains subject to independent review.
