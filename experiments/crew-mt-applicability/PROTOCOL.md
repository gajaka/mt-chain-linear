# Crew: applicability before integration

Status: REGISTERED FOR THE SOURCE GATE after user review. At registration,
no source gate, implementation or measurement has started. The earlier review
draft is preserved in `provenance/PROTOCOL-review-draft.md`.

The active project is `mt-chain-linear`. This experiment is separate from the
standalone chain result and `research/certificate-existence`. The original
framework in `vendor/ppg-lean` supplies definitions and conditional theorems;
its successful build does not establish an application to Crew.

## Success criterion

On the same pinned Crew code, with the same proposals, information and checking
obligations, the original MT/probability/hazard/stable-observable combination
must yield an additional confirmed production bug, a strictly stronger checked
guarantee under the same assumptions, or lower total cost at the same measured
reliability, with ablations identifying the contribution of the combination.

This is an empirical and formal comparison with specified alternatives, not
proof that no other method could obtain the result. Re-proving
`claim_exclusive`, adding library imports, or changing a controller's name does
not meet the criterion. No chain Theta(n) bound is transferred to Crew.

## 1. First gate: an existing process to which MT applies

This gate precedes a demonstrator, a new Lean model, a patch generator and any
performance or bug-discovery run. Its limit is **30 minutes** within the total
budget in section 6. Read-only source inspection is its principal activity.

The subject is Crew's existing task/job lifecycle at the revision below:
`src/kiro_crew/taskq/`, `src/kiro_crew/cron.py` and
`src/kiro_crew/cron_service/`, with their direct production callers and callees.
A repository-wide inventory of production random draws and retry entry points
may locate paths reachable from that lifecycle; it does not expand the subject
to unrelated Crew subsystems. Tests, fixtures,
random identifiers and random sampling in our earlier harness are not evidence
of a production resampling process. Record exclusions, not just promising hits.

Inspect at most three reachable candidate processes, ordered by source path
and line of their random-draw call, and select the first that satisfies the
whole table below. Inspect callees and callers needed to establish the path.
Do not choose by measured performance or by whether a counterexample appears.
If the inventory cannot be completed in time, report UNKNOWN rather than
claiming that no such process exists anywhere in Crew.

| Required item | Evidence required to pass the source gate |
| --- | --- |
| Actual stochastic mechanism | Production call path to a specific random draw, its distribution and its use in the transition; thread timing and a deterministic lease timeout alone are insufficient. |
| State and coordinates | State encoding, coordinate domains, initial law and explicit independence assumptions, with source locations. |
| Bad events | Predicates for user-relevant failed obligations, their coordinate dependencies, and a reachable failing state. A retry counter alone is not a bad-event definition. |
| Repair and locality | The existing operation selects a currently failed obligation and redraws the specified local coordinates; explain what remains unchanged and what deterministic bookkeeping accompanies it. |
| Conditional draw law | Justify fresh draws conditional on prior observations, including scheduler choices, caps, shared RNG state and any history-dependent backoff. Record the ideal-law/PRNG distinction. |
| Applicable original theorem | Name the exact original definitions and theorem, substitute the proposed state/operation/law, and list every remaining premise. Identify a concrete route to discharging them without strengthening assumptions after observing results. |
| Nontrivial interaction | At least two obligations interact through a repair. Identify actual invalidation and a potentially reusable observable; a single global restart with no selective hazard or reuse is insufficient for the full-combination claim. |

Random backoff is a lead, not a PASS: randomness plus repetition is not
Moser-Tardos resampling. The initial law, selection policy, footprint and
conditional distribution must match the theorem actually used. General
Markov behavior or a new drift argument cannot be relabeled as the original
MT theorem. A deterministic guarded SQL `claim` is not an MT process by itself.

A deterministic program could be the target of an *external* randomized repair
search. That is a different, legitimate experiment, but it is outside this
protocol. Absence of native MT structure does not prove that external approach
impossible. We will not add artificial random bits or switch to that approach
to turn a failed gate into a PASS.

Gate outcomes:

- **PASS_CANDIDATE:** the table has a source-backed candidate and an explicit
  theorem-obligation map. This permits the next stage; it is not a proof that
  the remaining premises hold.
- **STOP_NO_MATCH:** the inspected paths have no matching mechanism, or an
  identified law/locality mismatch prevents this instantiation. State the
  inspected scope and specific obstruction. Do not infer that all Crew is
  deterministic or that PPGraph has no application elsewhere.
- **STOP_UNKNOWN:** the time limit, missing source/call path, ambiguous law or
  missing theorem premise prevents a decision. No demonstrator follows.

Both STOP outcomes close this experiment. A random retry that cannot be mapped
to the original theorem is not partial success for the four-component claim.

### Registered search and repeat decisions

[SEARCH_PLAN.json](SEARCH_PLAN.json) fixes search patterns, scope, candidate
ordering and exclusions before source inspection. Dependency-library randomness
counts only on a traced production call path; its source/version must be
available and bound. Missing dependency source leaves UNKNOWN. Repeat decisions
made by Crew code are candidates; a human or external AI deciding to restart is
outside the native-process scope. Hybrid or unresolved cases do not pass.
Record all excluded mechanisms and the reason, plus UTC start/end and elapsed
time. Commit this protocol and search plan before the first source read.

## 2. One revision and explicit prior knowledge

The only subject revision is the article's public Crew snapshot:

```text
Repository: https://github.com/kirodotdev/KiroCrew
Revision:   909e0fc1938261df9c45fd74e86404abf22b5902
Archive:    71e8535d7d19dfdc1c7b53ad4b45af4694cf63985214215d680148347e25d71d
```

An existing local copy is at
`/Users/gajaka/projects/ppg-proof-repair/experiments/kiro-crew-comparison/sources/crew-909e0fc`.
Its `../SOURCE_MANIFEST.json` records 12,748 files and has SHA-256
`5d02035639b5ea3427aa9a88604990765d40482b9a8eacd242e189b7d4d1de5c`.
Before source analysis, validate that manifest against the actual snapshot.
Do not edit that snapshot or its historical evidence. Record every inspected
source path and hash in the new experiment's evidence.

The existing Python dependency lock has SHA-256
`40db5a4ff221b2ba1b9d823ece8d6ebd28df77531eccfd34d56f3089b80ab709` at
`/Users/gajaka/projects/ppg-proof-repair/experiments/kiro-crew-comparison/requirements-lock.txt`.
It is a prepared input, not a claim that this experiment has installed or run it.
The formal toolchain is Lean 4.35.0 / Mathlib at the root lockfile revision;
original PPGraph comes from `60151677e58704ce856c05a572904d681fd959f6` and is
bound by [the framework manifest](../../framework/SOURCE_MANIFEST.json).

If a repair is required, each candidate is an explicit patch to this one
snapshot, with a hash and declared behavioral differences. Do not import code
from the later PR #25130 base/head into the subject or silently replace the
pin. Later revisions may be inspected only to check whether a finding is known
or fixed; they are not alternative benchmark subjects.

Prior knowledge is substantial: known cancellation reproductions, random
task-store stress, and an expiry/answer-input counterexample with unresolved
production reachability already exist in the old project. They are not fresh
discoveries or held-out tests. The old README/checkpoint also predates the
framework restoration; its project-location statements are historical.

## 3. Formal and execution obligations after a source-gate PASS

Before collecting comparative outcomes, save a second-stage specification for
the selected process: exact state and law, bad events, selector, operations,
protected contract, hazard, observable, theorem roots, allowed inputs, tests,
baseline, candidate pool and metrics. These depend on the gate and cannot
honestly be filled in before reading the source. This specification also goes
to the user for review before implementation or measurement.

The following requirements cannot be relaxed in that specification:

| Component | Original reference | Additional Crew obligation |
| --- | --- | --- |
| MT and probability | `MoserTardos/Process/`, `MoserTardos/Probability/`, `Finite/Resampling/TableLaw.lean` | Instantiate the actual process and conditional law, including initialization and selector assumptions. `FiniteTable.nextDraw_fresh` alone is not a runtime bound. |
| Cost | `MoserTardos/Bounds/` | Name the bound and discharge all of its event/weight/convergence assumptions. A finite numerical fit is not an expected-cost theorem. |
| Semantic hazard | `Repair/SemanticHazards.lean` | Relate the computed scope to `RepairSemanticHazard.scope` on the actual allowed domain. Conservative overapproximation is safe only with its coverage proved and must be labeled. |
| Stable information | `Repair/ObservableAlgebra.lean` | Prove observation factorization and stability for the actual allowed operations before reuse. An open obligation or resource timeout is not a certificate. |
| Probabilistic quotient, if used | `Repair/ObservableKernel.lean` | Discharge `KernelClosed` and `GoodLocal` separately; deterministic stability does not automatically establish them. |
| Execution bridge | New, explicitly scoped evidence | Identify the model-to-code encoding, assumptions and independent rechecks. Sampled differential agreement is evidence, not universal implementation equivalence. |

Paths above are relative to `vendor/ppg-lean/PPGraph/`. See
[FrameworkAudit.lean](../../framework/FrameworkAudit.lean) for available roots.
Availability of all four components is not a proof that they jointly apply.

Keep a guarantee ledger with one row per change: prior guarantee, new
operation, required premise, supporting proof or execution evidence, and
guarantee retained/lost/unknown. In particular, history-conditioned AI proposals
must not be treated as fixed IID resampling. Any proposals used in a measured
comparison are saved once, shared with every arm, and fixed before the run.
Adding a candidate changes the experiment and cannot retroactively repair a
failed run or preserve an unproved cost guarantee.

For new mathematical claims require a strict Lean build, exact statement and
assumption review, allowed-axiom inspection, non-vacuity witnesses, and fresh
Nanoda checking of the selected proof closure. A missing check means pending,
not success. Do not assume the copied framework's earlier reported-axiom audit
is a fresh independent-kernel check of a Crew theorem.

## 4. Three success routes, reported separately

### A. Additional confirmed production bug

Require all of the following:

- A failing execution of unchanged pinned production code through real calls,
  plus evidence that real callers can create the required initial state and
  reach that path. A fixture-only deadline does not meet this condition.
- A documented intended property and a reproducible counterexample, separated
  from a stuck proof or resource UNKNOWN. The independent oracle confirms it.
- A comparison against the article's 18 reported findings and a bounded search
  of public issues, PRs and subsequent fixes. If already reported or fixed,
  classify it as reproduction, not an additional new production finding. If
  access or matching is inconclusive, novelty remains UNKNOWN and A does not
  pass. Public searches cannot prove absence from all private knowledge.
- With the same model, proposals, oracle and search budget, the full arm finds
  it and both the no-MT and no-hazard arms fail to find it in the registered
  runs. Report every seed and every timeout; do not select one lucky seed.
  The contribution of stable reuse and probability must also be documented
  under section 5, rather than implied by imports.

This supports bounded experimental attribution, not the claim that Kiro or any
other approach is unable to find the bug. The earlier known cancellation case
and already observed expiry trace cannot count as discoveries by a new search.

### B. Strictly stronger guarantee under the same assumptions

State old and new specifications `G_old`, `G_new` over one common semantic
domain and assumptions `A`. Prove `A -> (G_new -> G_old)` in Lean. Establish
strictness with a model/trace in that domain satisfying `A` and `G_old` but
not `G_new`. Also prove `G_new` for the selected Crew model and establish that
`A` is jointly satisfiable. Do not strengthen fairness, independence, workload
or atomicity assumptions to manufacture the improvement.

The strictness witness is for the logical specifications, not a demand for a
reachable counterexample to the newly proved theorem on the same correct
implementation. If the old formal statement is unavailable or cannot be
faithfully reconstructed and reviewed, strict comparison remains UNKNOWN.

A new user-relevant property such as an expected retry bound or absence of
starvation is allowed as an **additional guarantee**, reported separately. It
qualifies as a strict extension only through the same implication/strictness
test, for example with `G_new = G_old AND G_retry`, without extra assumptions.
A new stochastic assumption that the original guarantee did not need is an
explicit limitation, not a stronger guarantee under the same assumptions.

Show where MT, probability, hazard and the stable view enter the proof or its
checked construction. A failed proof attempt without them does not prove
that the property is unprovable by ordinary methods. Reproducing a known
theorem with different notation or a second kernel is not semantic strength.

### C. Lower total cost with the same measured reliability

Every arm receives the same accepted inputs, candidate proposals, dependency
information and independent obligations. A fresh full check of every final
accepted result and an independent replay of every retained/skipped obligation
are mandatory; these validation costs are included. Require zero wrong skips,
zero invalid acceptances and the same final success/failure outcomes. Zero
observed errors means exactly that, not universal execution safety.

Report first-use total cost and reuse cost separately. Count setup, source and
dependency acquisition, profiling, AI calls, model and proof construction,
compilation, proof checking, selection, repair, failed attempts and independent
validation. Shared work is charged equally; PPG-specific work is charged to
PPG. Earlier preparation is a sunk cost, disclosed with its available receipts;
unknown earlier costs are not set to zero or used to claim a total-cost win.
Report agent/human effort, wall time and compute time separately, including
parallel work. Do not reduce elapsed time to a test-call count.

For the final frozen workload, require at least five paired timed repetitions
in alternating order. The full arm must cost less than the strong baseline in
every pair after charging its measured preparation cost, and must pass the
same independent checks. Otherwise report no demonstrated C success. A reuse
or amortization result must give the measured workload count and break-even
point; hypothetical future repetitions cannot establish a first-use win.

## 5. Baseline, ablations and attribution

Choose and record the strongest applicable standard baseline before outcome
collection. Give it the same information and checks, including typed reuse,
dependency invalidation and cheap differential re-evaluation where applicable.
Do not remove a standard optimization just to create a benefit for PPG. The
article's original private proof scripts, generators and full cost records are
unavailable here; a local baseline is not a measured rerun of Kiro's pipeline.

Run or analyze these predeclared arms as appropriate to the success route:

| Arm | Change from the full combination |
| --- | --- |
| B: strong standard baseline | Same task/data/proposals/checks; ordinary methods and applicable standard reuse, without the proposed PPG operation. |
| Full | Original MT law plus justified hazard and stable reuse. All new obligations are discharged. |
| No use of MT structure | Analyze/explore the same native transition system with an ordinary method, without MT-guided selection of search choices or use of an MT theorem. Fix that method and its fair search order in the second-stage specification. Keep hazard/reuse, the same information and budgets, and the production random law. |
| No hazard selection | Perform all affected-obligation checks conservatively after each repair, retaining the other justified components. |
| No stable reuse | Recheck rather than reuse across an operation; retain the same process and hazard information. |
| No probability proof | Identical execution with the probability justification removed. Runtime can be identical; record the lost guarantee, not an invented speed difference. |

If the target is analysis of a native process rather than randomized repair
search, the no-MT arm is an alternative analysis/exploration method for that
same process, not a change to production semantics. Define it precisely in the
second-stage specification. If no fair implementable counterpart exists, the
requested ablation is UNKNOWN and the full-combination attribution is not met.

MT and its probability law are not independent operational switches. The last
arm removes a proof obligation's justification, not random draws from the code.
Use fixed seeds 0..19 for stochastic exploration comparisons, without cherry
picking, and equal per-arm limits set before those runs. These seeds describe
finite experiments, not a proof about ideal IID randomness. Record failures
and censored runs. If the budget does not allow all required arms, comparison
is incomplete. Removing a proof can leave outputs identical while weakening
the guarantee; removing an operational component must be assessed by outcomes
and full cost. These are different forms of contribution.

The no-hazard/no-reuse arms are diagnostic, not substitutes for B. A controller
with the same algorithm and data but different labels is a negative control;
equal performance there is expected. A familiar optimization under a PPG name
does not establish novelty or superiority over standard methods.

## 6. Budget, stop rules and evidence

The approved experiment has a **four-hour active elapsed-time ceiling**, from
starting the source gate through the final report. User-review pauses do not
consume that ceiling. Parallel work does not extend it; aggregate agent and
CPU time are reported separately. This document's preparation time remains part
of study preparation cost; it was not fully instrumented and must be labeled
unmeasured, not zero, in any end-to-end cost claim. No stage borrows from
the final reporting allocation or rolls into a new example.

| Stage | Maximum | Exit condition |
| --- | ---: | --- |
| Source identity and native MT applicability gate | 30 min | PASS_CANDIDATE or stop with scoped negative/UNKNOWN result |
| Exact second-stage specification and execution/proof obligations | 30 min | Reviewable fixed protocol; if no defensible map/baseline, stop |
| Minimal implementation, proof and source-model checks | 90 min | Required guarantees checked, or stop pending/UNKNOWN |
| Comparison, ablations and bounded public-history audit | 60 min | Complete registered evidence or incomplete result |
| Independent evidence review and final report | 30 min | Report every attempted route and unresolved item |

After source-gate failure, do not build a demonstrator. After success routes
A/B/C fail or remain unresolved, do not expand seeds, change revision, add
another benchmark, redefine success, or begin searching for a different
example. A new user instruction would be a separate study with its own record.
Timeout is UNKNOWN, not a counterexample or impossibility proof. Candidate
UNKNOWN is local until the total budget expires; a demonstrated wrong skip
or invalid acceptance immediately disqualifies that arm's claimed success.

Save new receipts under this directory, with new attempt names. Preserve the
reviewed protocol hash, source hashes, commands, versions, start/end times,
candidate origins, seeds, all outcomes and the guarantee ledger. Amendments
must be visible and preserve the previous protocol; deviations are reported,
not silently incorporated. Do not rewrite historical receipts in either repo.

Final outcome uses separate fields for gate, A, B, C, attribution, proof status
and execution correspondence. Overall success requires at least one completed
route **and** its corresponding attribution and checking obligations. A useful
partial result remains partial, even if all individual tests pass.

## Review checkpoint

The user reviewed the protocol and requested the source gate, with advance
registration of patterns, dependency policy and repeat-decision attribution.
Only that 30-minute gate is now authorized. Registration precedes all source
inspection in this gate. Subsequent outcomes belong in separate receipts and
a report; do not rewrite this registered document after seeing them.
