# Stochastic retry found; MT correspondence unresolved

**Outcome: STOP_UNKNOWN.** A bounded source inspection found internally
controlled stochastic retries in Kiro Crew. It did not establish their full
correspondence to an MT product-variable process. The experiment therefore
stopped before a demonstrator, a new Crew theorem or a comparative run.

This is an edited post-experiment report. The exact
[original report](https://github.com/gajaka/mt-chain-linear/blob/f9db8d3ec831f2b4d50c62016119aa84508479c1/experiments/crew-mt-applicability/REPORT.md)
remains available at the revision identified by the historical evidence hashes.
The current wording does not replace the original registration or receipts.

## Subject and coverage

The single subject revision was
[`909e0fc1938261df9c45fd74e86404abf22b5902`](https://github.com/kirodotdev/KiroCrew/tree/909e0fc1938261df9c45fd74e86404abf22b5902).
The declared scope was `taskq/`, `cron.py`, `cron_service/`, and their direct
production callers and callees. Tests, random identifiers and external
restart decisions were not counted as native MT mechanisms.

| Recorded item | Value |
|---|---|
| Inspection start UTC | 2026-11-05 14:23:15.696130 |
| Inspection end UTC | 2026-11-05 14:33:45.378500 |
| Elapsed source gate | 629.682370 seconds |
| Source-gate ceiling | 1800 seconds |
| Manifest-listed Crew files with unchanged hashes | 12,748 |
| Crew files examined in detail | 18 |

A repository-wide text inventory located random-source, retry and lifecycle
references. Text-match counts were not counts of independent stochastic
mechanisms. Detailed review also covered `croniter`, Python `random` and two
environment/version metadata files. Checking source identity is distinct from
semantically reviewing every file. Exact read ranges and hashes are in
[INSPECTED_SOURCES.json](evidence/gate-001/INSPECTED_SOURCES.json), with coverage
limits in [INVENTORY_COVERAGE.json](evidence/gate-001/INVENTORY_COVERAGE.json).

## Inspected mechanisms

All production-source references below refer to the single revision above.

### Scheduled timing

```text
enabled + unclaimed + due -> random delay -> sleep -> callback
```

The due selector and delay use are in
[`cron.py`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/cron.py#L3523),
particularly lines 3523, 3569-3577, 3613-3615, 3682 and 3705-3707. Jitter draws
are in
[`schedule.py:476-508`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/cron_service/schedule.py#L476).
The `croniter==2.0.7` R/r-expression branch was recorded as part of this timing
process; no production R/r input was executed to establish its runtime reach.

Healthy periodic work also follows this path, so the due selector is not a
selector of a violated obligation. Manual, strict and one-shot paths may use
zero jitter. Randomizing pre-execution timing does not by itself establish
local resampling of a failed MT event. See
[CRON_REVIEW.json](evidence/gate-001/CRON_REVIEW.json).

### Recovery-ladder retries

```text
recoverable stop -> attempt policy -> retry/escalate/notify/stop
                 -> random wait -> reclaim -> execute again
```

The production caller is
[`task_executor.py:971-1037`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/task_executor.py#L971).
The recovery ladder records failure and decides continuation in
[`ladder.py:398-427`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/recovery/ladder.py#L398).
The draw in
[`policy.py:127-134`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/recovery/policy.py#L127)
is `raw/2 + U*(raw/2)`, with an attempt-dependent raw delay and optional
server floor/cap. Continuation is selected by code; the top ladder level
requires a user restart and is outside the native-process scope.

The sampled quantity is waiting time. The source does not supply a product
law for the retried provider's success. Attempts, deadlines and ownership
state change as well, and retry exhaustion can end with a failed obligation.
No complete correspondence to MT coordinate replacement was established.

### Dependency-coordinator retries

```text
provider exception -> dependency failure -> scope attempt/phase update
                   -> backoff -> monitor tick -> capacity-controlled retry
```

The exception path is
[`subagent_manager/run.py:1914-1933`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/subagent_manager/run.py#L1914).
The coordinator updates state in
[`dependency.py:727-783`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/taskq/dependency.py#L727),
uses the same random-backoff sampler at 667-669, and calculates retry times at
806-826. Monitor calls are in
[`monitoring.py:322-345`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/subagent_manager/monitoring.py#L322);
probes and capacity wakes occur at `dependency.py:1003-1052`.

This is a genuine internal stochastic repeat mechanism. Its shared waiters,
restored state, deadlines and external provider recovery still lack the
required product-state and local-resampling correspondence. See
[TASKQ_REVIEW.md](evidence/gate-001/TASKQ_REVIEW.md) and its JSON receipt.

## Other mechanisms excluded

| Mechanism | Source location | Reason |
|---|---|---|
| Guarded claim and conflict retry | `taskq/store.py:877-940` | Deterministic guarded SQL; repeated claiming is not a random redraw. |
| Next-task ordering | `taskq/store.py:1601-1627` | Oldest eligible row with deterministic ordering. |
| Lost-owner reconciliation | `taskq/reconcile.py:148-179`, `taskq/model.py:183-191` | Code-controlled requeue with deterministic raw backoff. |
| Operator input or manual execution | `taskq/adapters/runner.py:1718-1755`, `cron.py:3154-3177` | External continuation rather than the inspected native random retry. |
| Unrelated inventory hits and test generation | Registered search scope | Textual randomness or harness sampling does not establish a production MT process. |

## Missing MT premises

The [formal review](evidence/gate-001/FORMAL_REVIEW.md) identifies the relevant
[MT process definitions](../../library/MT/MoserTardos/Process/) and
[cost hypotheses](../../library/MT/MoserTardos/Bounds/OccurrenceExpectation.lean).

| Obligation | Finding |
|---|---|
| Production randomness and internal retry decision | Present in the two retry mechanisms. |
| Full state, bad events and fixed coordinate footprints | Not established for complete lifecycle state and external outcomes. |
| Local fresh replacement | Timing is sampled; the failed external condition has no supplied redraw law. |
| Initial product law | Not established for persisted lifecycle state. |
| Selector correspondence | Due work differs from failed-event selection; a matching retry selector map was not supplied. |
| Successful-repair cost bound | Required event-probability and convergence premises were not discharged. Retry caps can end in failure. |
| Hazard and stable observable reuse | Not instantiated because the process correspondence remains unresolved. |

History-dependent scaling of a fresh uniform draw can model variable backoff;
this alone is neither an impossibility proof nor a complete MT encoding.
Continuous state and a shared PRNG also do not, by themselves, decide
applicability. The model must still account for the whole transition and
justify its probability assumptions.

## Evidence limits and conclusion

The gate used the registered revision and preserved the original protocol,
search plan and source hashes. Concurrent review departed from a literal
sequential reading of the candidate order; all three mechanisms were reported.
The R/r library branch was grouped with scheduled timing during inspection.
Some source queries failed before corrected queries completed; the retained
receipts distinguish those errors from completed searches. These procedural
limits remain part of interpreting the bounded result.

No Crew module was executed, and no test, new Lean proof, patch, performance
run or ablation was performed. The gate duration measures source inspection,
not the total cost of an integrated repair method. Earlier preparation cost
was not fully measured.

The aggregate outcome is **STOP_UNKNOWN**, as recorded by
[FORMAL_VERDICT.json](evidence/gate-001/FORMAL_VERDICT.json) and the unchanged
`RESULT.json`. No later experimental stage ran. This finding rejects no
possible encoding universally and leaves the concrete chain and its
certificate-separation results unchanged.
