# Native MT applicability gate: scope and criteria

This is a post-experiment account of the source gate. The
[registered protocol](https://github.com/gajaka/mt-chain-linear/blob/f9db8d3ec831f2b4d50c62016119aa84508479c1/experiments/crew-mt-applicability/PROTOCOL.md)
retains the exact text and hashes used before inspection. This edited account
is not a new preregistration. The completed outcome is **STOP_UNKNOWN**.

## Question

Can an existing stochastic retry mechanism be identified as an instance of
the MT product-variable process, with its bad events, local resampling law,
initialization and theorem premises justified from source?

The subject was the task/job lifecycle in
[Kiro Crew](https://github.com/kirodotdev/KiroCrew/tree/909e0fc1938261df9c45fd74e86404abf22b5902),
revision `909e0fc1938261df9c45fd74e86404abf22b5902`: `taskq/`, `cron.py`,
`cron_service/`, and their direct production callers and callees. Only this
revision was evaluated. Random delays and repeated work alone were not
sufficient evidence of MT resampling.

## Required correspondence

| Item | Required evidence |
|---|---|
| Production randomness | A reachable draw, its distribution and its role in the transition; timing races and deterministic lease expiry alone do not qualify. |
| Product state | Explicit coordinates, domains, initial law and independence assumptions, related to the complete production state. |
| Bad events | User-relevant failed obligations, a reachable failure and fixed coordinate footprints. |
| Local repair | Selection of a currently failed obligation; replacement of its footprint while every other modeled coordinate remains fixed. |
| Conditional law | Fresh draws justified conditional on prior observations and selector choices. A PRNG call is not a proof of an ideal IID law. |
| Cost theorem | A named MT theorem with its initialization, measurability and convergence premises discharged. |
| Hazard or reuse, if applied | A justified invalidation scope and stable observable for the actual allowed operations. Their abstract definitions do not establish an application. |

The [MT process](../../library/MT/MoserTardos/Process/) and
[expected-cost theory](../../library/MT/MoserTardos/Bounds/) state the relevant
mathematical obligations. General Markov behavior or a new drift argument
cannot substitute silently for a particular MT theorem.

## Inspection rules

The source gate had a 30-minute ceiling. The
[search plan](SEARCH_PLAN.json) fixed the patterns, scope and exclusions.
Dependency-library randomness counted only on a traced production call path.
A repeat chosen by the program was distinguished from a human or external
agent restarting it. External randomized repair search was outside the gate.

At most three candidate mechanisms were to be inspected. The actual report
records scheduled timing, recovery-ladder retries and dependency-coordinator
retries. Concurrent review departed from a literal sequential reading of the
candidate order; all three were reported, without selecting by favorable
outcomes.

## Outcomes and stop rule

- `PASS_CANDIDATE`: a source-supported process and explicit theorem-premise map
  justify further analysis; this is not yet a proof of the premises.
- `STOP_NO_MATCH`: a specific inspected representation fails the required
  correspondence; the conclusion is limited to that representation and scope.
- `STOP_UNKNOWN`: source, distribution, initialization or theorem premises
  remain unresolved within the gate budget.

Both STOP outcomes end the experiment before implementation or comparison.
A retry cap can bound attempts while leaving an obligation failed; it is not
an MT convergence guarantee. Failure to establish a correspondence does not
prove that every possible encoding is impossible.

The gate ended after 629.682370 seconds with `STOP_UNKNOWN`. No demonstrator,
new Crew theorem, bug-discovery comparison or performance comparison followed.
See [REPORT.md](REPORT.md) and the unchanged source-inspection receipts.
