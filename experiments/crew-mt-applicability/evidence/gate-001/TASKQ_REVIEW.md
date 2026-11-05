# Task-queue source gate review

The dependency coordinator is a real, internally triggered stochastic retry
mechanism. It is not an external human/AI restart. The inspected code does not
supply a mapping to the original MT product-variable resampling process.

The complete facts, line ranges, exclusions, limitations and source hashes are
in `TASKQ_REVIEW.json`; exact adaptive queries, their errors, read ranges and
timestamps are in `TASKQ_READ_LOG.json`. No source code, tests or proofs ran.

The decisive path is provider exception -> coordinator.report -> equal-jitter
delay -> monitor tick -> capacity-controlled wake. See run.py:1914-1933,
dependency.py:727-783 and 806-826, policy.py:104-134, monitoring.py:322-345, and
dependency.py:1003-1052. The scheduler redraws timing, not the failed external
dependency. The provider's future behavior has no supplied product law.

History-dependent backoff alone is not a mathematical impossibility argument:
normalizing a fresh uniform draw removes the varying scale. It still leaves
external-state bad-event dependence, initialization and repair-locality
obligations unestablished. No claim excludes every possible re-encoding.

The guarded SQL claim and oldest-first conflict retries are deterministic
(store.py:877-940,1601-1627). Reconciliation is internal but uses raw deterministic
backoff (reconcile.py:148-179; model.py:183-191). An operator answer is distinct
from native retry (adapters/runner.py:1718-1755).
