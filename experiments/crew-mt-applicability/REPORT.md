# Crew source gate: native randomness found, MT correspondence unresolved

**Outcome: STOP_UNKNOWN.** Crew contains internally controlled stochastic
retries. The inspected mechanisms do not supply a source-supported
instantiation of the original MT process and its theorem premises. The
registered stop rule therefore ends this experiment before a demonstrator,
new Crew proof or comparative run.

This is a bounded source review. It rejects several direct interpretations
as established MT instances; it does not prove that every possible encoding
is impossible or determine the usefulness of PPGraph in general.

## Registration, identity and time

The [protocol](PROTOCOL.md) and [search plan](SEARCH_PLAN.json) were committed
before the first Crew source search in this gate:

```text
Registration commit: ecd0d36573373986031630710d77debc0c8290e2
PROTOCOL.md SHA-256: 1c1c1ce8c4e622cb8563b00f50983c5b8c13a9eec27280b7ae9814ad2d4750f0
SEARCH_PLAN SHA-256: b2d6c10fc46bdf93a366a39274c19d3579531a7c75a7b67c762f028fa866fd97
Crew revision:      909e0fc1938261df9c45fd74e86404abf22b5902
Start UTC:          2026-11-05 14:23:15.696130
End UTC:            2026-11-05 14:33:45.378500
Elapsed:            629.682370 seconds (10 minutes 29.682370 seconds)
Limit:              1800 seconds
```

Belgrade local time was 15:23:15 to 15:33:45. The end above closes source
inspection and identity checks; report preparation and final evidence review
are recorded separately. UTC timestamps determine the displayed duration.
Monotonic stamps were retained but were obtained in different processes and
were not subtracted to calculate it.

All **12,748 manifest-listed Crew files** matched their original SHA-256
values before and after inspection. That identity check does not mean that
all files were semantically reviewed. Detailed inspection covered **18 Crew
files**, plus `croniter` and Python `random` source and two environment/version
metadata files. Exact paths and hashes are in
[INSPECTED_SOURCES.json](evidence/gate-001/INSPECTED_SOURCES.json).
Original proof definitions were inspected separately, with hashes in
[FORMAL_INPUTS.json](evidence/gate-001/FORMAL_INPUTS.json).

## Search coverage

The predeclared patterns covered `random.`, `secrets.`, `os.urandom`,
`numpy.random`/`np.random`, relevant imports, `jitter`, `backoff`, `tenacity`,
`retry`/`retries`/`retrying`, and lifecycle decisions such as lease, claim,
expiry, reschedule and dispatch. Follow-ups traced aliases and callers of
matched functions. Dependency-library randomness counted when a production
call path reached that library; library source was read without importing or
executing it.

| Initial text inventory | Matching lines | Files with matches |
| --- | ---: | ---: |
| Random sources/imports | 383 | 165 |
| Retry/backoff terms | 3,711 | 681 |
| Lifecycle decisions | 22,130 | 1,238 |

These are text matches, including comments and unrelated subsystems, not
counts of random mechanisms. The declared subject was `taskq/`, `cron.py`,
`cron_service/` and their direct production callers/callees. Other matches
remain inventory-only; they were not all followed or proved unreachable.
[INVENTORY_COVERAGE.json](evidence/gate-001/INVENTORY_COVERAGE.json) records
that distinction. Full query outputs and adaptive query reasons are retained.

Three conceptual processes were inspected: scheduled timing, recovery-ladder
retries and dependency-scope retries. The latter two share the same jitter
sampler but have different retry decisions. No fourth repair process or
alternative revision was evaluated.

## What the code actually does

All Crew line references below refer to the single pinned revision. The
review receipts contain read ranges, source hashes and supporting excerpts.

### 1. Scheduled execution: random delay before ordinary work

```text
enabled + unclaimed + due
          |
          v
draw schedule jitter -> sleep -> execute callback
          |
          v
next scheduled execution, including after success
```

The due selector is in
[`cron.py:3523`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/cron.py#L3523)
and `3569-3577`; task creation is at `3613-3615`. Actual jitter draws are in
[`schedule.py:483`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/cron_service/schedule.py#L483),
`485`, `504`, `507` and `508`. The caller stores the sampled delay at
[`cron.py:3682`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/cron.py#L3682)
and sleeps at `3705-3707`.

The installed `croniter==2.0.7` source also contains an R/r-expression random
branch (`croniter.py:993-994`) reachable in the static expansion call graph
from `schedule.py:493`. It is recorded as a library branch of this same timing
process, not a separate failed-obligation repair. No production R/r input was
executed to establish runtime reachability of that branch.

The decision to run scheduled work is internal. Healthy periodic work also
runs; selection does not require a violated certificate. Manual `run_job`
at `cron.py:3154-3177` is an external trigger and gets zero execution jitter
at `3682`. Strict/one-shot paths also return zero jitter in `schedule.py:476-487`.

**Direct correspondence rejected:** pre-execution timing jitter is not, by
itself, selection and local resampling of a failed obligation. Receipt:
[CRON_REVIEW.json](evidence/gate-001/CRON_REVIEW.json).

### 2. Recovery ladder: code decides whether to retry

```text
recoverable stop observed by task executor
          |
          v
record failure -> attempt policy -> retry / escalate / notify / give up
          |
          v
draw waiting time -> persist recovering -> wait -> reclaim -> run again
```

The actual caller catches a recoverable stop in
[`task_executor.py:971`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/task_executor.py#L971),
calls admission at `990`, applies retry limits at `997-1007`, persists the
recovering state at `1016`, waits at `1035` and reclaims at `1037`.
[`adapters/runner.py:1380`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/taskq/adapters/runner.py#L1380)
calls the recovery ladder.

[`ladder.py:398`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/recovery/ladder.py#L398)
increments tracked failures; `400-427` decides retry/escalation/notification.
The actual draw is at
[`policy.py:130`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/recovery/policy.py#L130):
`raw/2 + U*(raw/2)`, with an attempt-dependent raw delay and optional server
floor/cap at `127-134`. This describes the source computation; an ideal IID
law for U is a further modeling obligation, not proved by reading the PRNG.

This retry decision belongs to code, even when the task executes an AI
payload. It is distinct from an external agent choosing to resubmit a task.
The top ladder layer explicitly requires a user restart and has
`automatic=False` at `ladder.py:170-176`; that external continuation is excluded.

**Mapping unresolved:** the sampled value is waiting time. Success of the
retried runtime/provider is not supplied as a product-coordinate draw.
Attempts, deadlines and ownership state also change. Exhaustion can end a
failed step (`task_executor.py:1008-1015`), rather than make every obligation
good. The natural complete runtime state has not been related to the original
MT coordinate-replacement transition.

### 3. Dependency coordinator: real stochastic retry shared across waiters

```text
classified provider exception -> report dependency failure
          |
          v
update scope attempts/phase -> backoff or server retry time
          |
          v
monitor tick -> probe/capacity wake -> retry work
```

The production exception path is
[`subagent_manager/run.py:1914`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/subagent_manager/run.py#L1914)
through `1933`. The coordinator updates attempts, phases and waiters in
[`dependency.py:727`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/taskq/dependency.py#L727)
through `783`. It delegates the random backoff at `667-669` to the same
`policy.py:130` draw. Retry-time calculation at `806-826` also honors server
floors. The monitor calls the coordinator in
[`monitoring.py:322`](https://github.com/kirodotdev/KiroCrew/blob/909e0fc1938261df9c45fd74e86404abf22b5902/src/kiro_crew/subagent_manager/monitoring.py#L322)
through `345`; `dependency.py:1003-1052` implements probes and capacity wakes.

This is another internal stochastic repeat decision. It still leaves the
external provider's recovery unmodeled by a redraw law. Persistent state may
be restored from previous execution, and budget/deadline exhaustion can fail
waiters (`727-783`, `828-840`). No independent product initialization or
original MT theorem instantiation was established. Receipt:
[TASKQ_REVIEW.json](evidence/gate-001/TASKQ_REVIEW.json).

## Other mechanisms inspected and excluded

| Mechanism | Pinned source | Reason |
| --- | --- | --- |
| `claim` and conflict retry | `taskq/store.py:877-940` | Guarded SQL; `claim_next` repeats up to eight times, without random redraw. |
| Choosing the next task | `taskq/store.py:1601-1627` | Oldest eligible row with deterministic ordering; no random worker choice established. |
| Lost-owner reconciliation | `taskq/reconcile.py:148-179`, `taskq/model.py:183-191` | Code-controlled requeue; stored recovery delay uses deterministic raw backoff. |
| Operator answers input | `taskq/adapters/runner.py:1718-1755` | External trigger, separate from the coordinator's internal retry. |
| Manual cron execution | `cron.py:3154-3177`, `3682` | External trigger; no execution jitter on that path. |
| Top-level recovery continuation | `recovery/ladder.py:170-176`, `400-427` | Automatic recovery stops and user action is required. |
| Imports, comments, identifiers, unrelated subsystem hits | Registered inventory and coverage receipt | Textual randomness is insufficient; paths outside the declared lifecycle remain inventory-only. |
| Earlier random stress/reproduction harnesses | Historical experiment, outside pinned production source | External test generation is not a native Crew resampling process. |

## Why the MT premises remain open

The original `resample` replaces exactly the selected footprint and preserves
every other coordinate (`Process/Basic.lean:55-56,90-94`). `MTProcess` requires
bad events dependent only on their fixed footprints, and faithful selection
of an actually violated event (`Process/Process.lean:32-35,55-57`). Paths here
are relative to `vendor/ppg-lean/PPGraph/MoserTardos/`.

| Obligation | Gate evidence |
| --- | --- |
| Production randomness and internal repeat decision | Present in the two retry mechanisms. |
| State coordinates and bad-event footprint correspondence | Not established for complete Crew state and external outcomes. |
| Local fresh redraw implementing the repair | Random waiting time identified; failed runtime/provider condition is not itself resampled by the inspected call. No refinement proving the required complete correspondence was supplied. |
| Initial product law | Not established for existing persisted lifecycle state. |
| Selector correspondence | Scheduled due work differs from failed-event selection. No matching MT selector correspondence was supplied for the retry coordinators. |
| Expected successful-repair bound | No convergence/weight premises discharged; a retry cap can end in failure. |
| Hazard and stable observable reuse | Not instantiated because the underlying process correspondence is unresolved. |

History dependence of a backoff range alone is not an impossibility proof:
one can transform a fixed-law uniform by history-dependent scale and offset.
That observation supplies random inputs, not all missing MT structure.
Continuous/unbounded state and use of a shared PRNG also do not independently
prove impossibility. Conversely, they cannot be silently equated with the
finite ideal table process.

`FiniteTable.nextDraw_fresh` proves a conditional law for its constructed table
process under its stated premises; it is not a convergence theorem or a proof
of Python-PRNG/source correspondence. The representative
`randomInitETLog_le_sum` also needs product initialization, its concrete
first-violated trajectory, measurable event bounds and weight inequalities.
These were not established here. The independent
[formal review](evidence/gate-001/FORMAL_REVIEW.md) gives exact definitions and
the [verdict](evidence/gate-001/FORMAL_VERDICT.json) recommends `STOP_UNKNOWN`.

## Evidence quality and procedural limits

The reviewed draft was preserved before registration. Protocol and search-plan
hashes stayed unchanged. Source hashes were checked before and after; original
Crew, old receipts and formal proof bodies were not edited.

Reviews ran concurrently. This differs from a literal sequential reading of
the registered candidate ordering; the three processes above were all
reported, and none was selected for favorable comparative outcomes. The R/r
library branch was grouped with the same scheduled-timing process during
inspection, as documented in the cron review. No experimental outcomes were
used to choose that grouping, but it was an interpretive choice after reading.

Some adaptive queries used guessed nonexistent directories and returned errors.
Those errors and corrected queries are retained. The root reader initially
raised before saving one failed query; its error was recorded retrospectively
in [QUERY_ERROR.json](evidence/gate-001/QUERY_ERROR.json). Its original helper
was retained, then changed to save failed-query receipts and always include
filenames. No failed query is represented as a completed search.

No Crew module was imported/executed; no test, Lean proof, network search,
patch, performance run or ablation was performed under this gate. This report
therefore makes no claim of a new bug, a stronger code guarantee or saved
runtime. The gate duration is elapsed inspection time, not aggregate reviewer
CPU/AI effort or a measured full cost of an integrated method. Preparation cost
before the gate was not fully instrumented and is not treated as zero.

## Disposition

The required complete correspondence is missing, so the registered outcome is
**STOP_UNKNOWN**, rather than PASS_CANDIDATE or a universal non-applicability
theorem. Success routes A/B/C remain **NOT RUN**. No demonstrator follows and
no alternate revision, new example or externally randomized repair search is
started. The existing chain and certificate-separation results are unaffected.

The read-only result is reviewable through the source links above, the exact
read receipts, [START.json](evidence/gate-001/START.json),
[END.json](evidence/gate-001/END.json), and the accompanying `RESULT.json`.
