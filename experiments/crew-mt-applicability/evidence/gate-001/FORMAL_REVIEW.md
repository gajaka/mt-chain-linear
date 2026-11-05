# Original MT hypotheses: independent source review

This review reads the copied original Lean definitions; it does not execute
Crew, inspect a new Crew candidate, build Lean, or prove a new result. The
inputs and read ranges are bound in `FORMAL_INPUTS.json`. Candidate-specific
source conclusions remain the responsibility of the separate code audit.

## Exact mapping obligations

Paths below are relative to `vendor/ppg-lean/PPGraph/`.

| Requirement | Definition or result | Consequence for the gate |
| --- | --- | --- |
| Coordinate spaces and laws | `MoserTardos/Process/Basic.lean:43-47`, `VarSpaces` | A fixed probability law is supplied for each coordinate. The model must identify those coordinates and the relation to production state. |
| Exact local update | `Basic.lean:55-56`, `resample`; preservation at `90-94` | Selected coordinates are replaced by the fresh assignment; every other coordinate remains identical. Deterministic updates to counters or external effects need a separate execution/refinement account, not an omitted state field. |
| Bad events and dependence | `MoserTardos/Process/Process.lean:32-35`, `MTProcess` | Each bad event has a fixed finite footprint and depends only on it. A retry being scheduled does not supply these predicates or dependencies. |
| Violated-event selection | `Process.lean:55-57`, `faithful`; `Finite/Resampling/Basic.lean:169-185`, `Admissible` | Active resampling selects an actually violated event. A periodic timer firing without a failed obligation does not satisfy this condition merely because it draws a delay. |
| Actual selector used by the representative bound | `MoserTardos/Process/RandomTrajectory.lean:95-97`, `pickFirstViolated` | This concrete trajectory uses the canonical finite-list first-violated policy. A different scheduler needs a matching theorem or an explicit correspondence; the displayed bound is not a free scheduler parameter. |
| Adaptive table construction | `Finite/Resampling/Table.lean:39-44,50-67` | The finite result assumes finite coordinate domains and finitely many coordinates. Footprint choice is a function of current state. Initialization reads only row zero (`InitialLocal`); a constant initializer is allowed for this freshness result. |
| Fresh conditional product law | `Finite/Resampling/TableLaw.lean:160-164`, `nextDraw_fresh` | Under measurable, InitialLocal initialization, the next table draw has the product-law conditional distribution given the table process's state prefix. This is a property of the constructed ideal table model, not a theorem that a Python PRNG or an external server has that law. |
| Random initialization for the representative cost bound | `MoserTardos/Process/RandomInitialization.lean:28-30` and `MoserTardos/Bounds/OccurrenceExpectation.lean:90-98` | `randomInitETLog_le_sum` concerns the product-initialized process. The fact that a constant initializer satisfies the freshness lemma does not transfer this random-initialization cost bound to an arbitrary warm start. |
| Additional convergence premises | `OccurrenceExpectation.lean:92-98` | Besides measurable bad events and their probability bounds, the theorem requires `p <= x` and `p(alpha) * product_(beta in plusNeighbors alpha) (1+x(beta)) <= x(alpha)`. Merely identifying an MT update does not establish these inequalities. |
| Finite executable correspondence | `Finite/Resampling/Basic.lean:142-146,159-185,236-243` | The finite kernel is a product update on the selected footprint, with Kronecker equality outside. Embedding Boolean bad events into MT preserves their actual footprints and dependence; it does not accept an arbitrary retry kernel. |

The freshness result's finite-domain restriction is specific to that result.
The general `VarSpaces` interface allows other domains, so an unbounded or
continuous state is not by itself a proof that no original theorem can apply.
It does require selecting and discharging the hypotheses of an appropriate
result rather than quoting the finite table theorem unchanged.

## Avoid a false impossibility argument

A delay whose range depends on an attempt count is not by itself proof that
an MT representation is impossible. In an ideal probabilistic model one can
write, for example, `delay = a(history) + b(history) * U`, with a fresh fixed-law
uniform `U`. This represents the random input, not automatically the entire
repair as an MT coordinate replacement. It leaves the state encoding,
deterministic history update, selected bad event, footprint dependencies,
initialization and source-to-model correspondence to establish.

Likewise, a probe's success can depend on an external provider, resource
availability, a clock and concurrent writes. Independent jitter does not make
those outcomes independent redraws. No distribution or liveness guarantee for
an external outcome should be inferred from the random sleep alone.

A retry cap or deadline can end execution while its failed obligation remains
false. Such failure/escalation is not convergence to all-good MT state. A
finite bound obtained by counting the cap is distinct from the original
expected successful-repair guarantee.

A generator shared across callbacks is not automatically a refutation of an
ideal IID specification, but neither does its existence prove that
specification. The actual PRNG and the ideal law must remain distinguished.

## Permissible conclusions

- A source-supported native stochastic candidate is only `PASS_CANDIDATE` until
  the full map and remaining theorem premises are supplied.
- An actual mismatch in the proposed direct representation, or no qualifying
  process in the audited paths, supports a scoped `STOP_NO_MATCH`.
- Incomplete call tracing, missing distribution/initialization evidence, or
  failure to construct a map within the cap supports `STOP_UNKNOWN`, not a
  theorem that every possible encoding is impossible.
- A negative native-process gate does not rule out a separately designed
  external randomized repair/search algorithm. That alternative is excluded
  from this experiment by its registered scope, not by the MT mathematics.

No conclusion about all Crew, all randomized retry algorithms, general PPG
usefulness, or the existing chain Theta(n) proof follows from this review.

## Review of the task-queue findings

After inspecting `TASKQ_REVIEW.md` and `TASKQ_REVIEW.json`, the recommended
aggregate status is **STOP_UNKNOWN**. The exact input report hashes are in
`FORMAL_VERDICT.json`. Native stochastic retry exists; the outstanding issue
is the original MT mapping, not absence of randomness.

The natural task/schedule encoding has concrete mismatches: randomness changes
waiting time, failed external dependencies have no supplied product-coordinate
law, additional history-dependent state changes occur, and exhaustion may end
with failed waiters. These reject that direct interpretation as an established
MT instance. They do not prove that every possible encoding is impossible.

For cron-only pre-execution jitter, failing to select an actually violated
event can support `NO_MATCH` for that direct candidate. The aggregate remains
UNKNOWN because genuinely stochastic retry mechanisms were found but their
required theorem/implementation correspondence has not been established.
This follows the registered rule that a missing theorem premise yields UNKNOWN.
No demonstrator, new example or new randomization follows this outcome.
