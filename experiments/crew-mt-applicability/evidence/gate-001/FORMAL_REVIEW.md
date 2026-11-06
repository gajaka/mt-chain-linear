# MT hypotheses relevant to the source gate

This is an edited post-experiment account of the formal review. The exact
[original review](https://github.com/gajaka/mt-chain-linear/blob/f9db8d3ec831f2b4d50c62016119aa84508479c1/experiments/crew-mt-applicability/evidence/gate-001/FORMAL_REVIEW.md)
is preserved at the revision identified by the historical receipts. No new
Crew proof or execution is asserted by this account.

## Required mathematical map

| Requirement | Current theory reference | Consequence for an application |
|---|---|---|
| Coordinates and laws | [Process/Basic.lean](../../../../library/MT/MoserTardos/Process/Basic.lean), `VarSpaces`, `MTState` | Identify each coordinate domain and fixed probability law, and relate the product state to the production state. |
| Exact local replacement | The same file, `resample`, `resample_fixes_outside` | Replace only the selected footprint. Counters, ownership changes and external effects need an explicit state/refinement account. |
| Local bad events | [Process/Process.lean](../../../../library/MT/MoserTardos/Process/Process.lean), `MTProcess`, `depends_only_on` | Every bad event has a fixed footprint on which its truth depends. A scheduled retry alone does not define such an event. |
| Violated-event selection | The same file, `faithful` | A resampling step must select an obligation that is currently violated. Periodic healthy work does not satisfy this merely because its timing is random. |
| Selector for the representative bound | [RandomTrajectory.lean](../../../../library/MT/MoserTardos/Process/RandomTrajectory.lean), `pickFirstViolated` | The concrete trajectory uses first-violated selection. A different scheduler requires an applicable theorem or a proved correspondence. |
| Product initialization | [RandomInitialization.lean](../../../../library/MT/MoserTardos/Process/RandomInitialization.lean) | The random-initialization result does not automatically cover arbitrary persisted state. |
| Expected-cost premises | [OccurrenceExpectation.lean](../../../../library/MT/MoserTardos/Bounds/OccurrenceExpectation.lean), `randomInitETLog_le_sum` | Establish measurable bad events, their product-law probability bounds and the stated weight inequalities before quoting the cost bound. |

Freshness of the ideal random input and its correspondence to the production
source are separate obligations. A constructed table law does not, by itself,
prove that a Python PRNG or an external provider has that law.

## What the inspected mechanisms leave unresolved

A history-dependent delay can have the form

```text
delay = a(history) + b(history) * U
```

with a fixed-law fresh uniform U in an ideal model. The changing scale alone
does not prove MT impossible. It also does not establish the entire repair
transition: state encoding, deterministic bookkeeping, failed-event
footprints, initialization and source correspondence remain necessary.

Similarly, independent jitter does not turn a provider's future success into
an independent coordinate draw. A retry cap or deadline can terminate with
failed waiters, which differs from reaching an all-good MT state. Unbounded
state and a shared PRNG are modeling issues, not stand-alone impossibility
arguments.

## Reviewed outcome

The [task-queue findings](TASKQ_REVIEW.md) identify an internally triggered
stochastic retry, and the [verdict](FORMAL_VERDICT.json) records the aggregate
recommendation **STOP_UNKNOWN**. The missing item is a complete MT mapping,
not production randomness.

For scheduled timing, the direct interpretation also lacks selection of an
actually violated event. For the retry coordinators, waiting time is sampled
but the failed external condition has no supplied product-coordinate law;
additional state changes and exhaustion remain unmodeled by the proposed
resampling interpretation. These facts leave the attempted instantiation
unestablished. They do not exclude every possible encoding or alter the
concrete chain's Theta(n) theorem.
