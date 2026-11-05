# Theorem scope and local repair

The theorem inventory counts explicit Lean declarations. It includes definition
accessors, structural laws and applications of general results, alongside the
main mathematical arguments. Proof length does not classify their usefulness.

## Changes on 2026-10-28

The former `linear_strict_not_equiv_aux : True` declaration and its `#check`
were removed. The actual convexity theorem `equiv_convex` remains proved.
`linear_cert_le_iff_le` was renamed to `linear_cert_le_of_le`: its statement
establishes order preservation, with no converse for arbitrary families.

In [Core/Repair.lean](../PPGraph/Core/Repair.lean), four former statements were
replaced with before/after properties of an explicit local data update. A new
`repair_restores` theorem proves target restoration. That first cleanup kept the declaration count
unchanged: one placeholder was removed and one restoration theorem was
added. Repair has nine declarations; ParametricQuotient has twenty-five.

## Local data model

Slots and values have type `V`; initially, each slot stores its own value.
The original predicate `G.invariant_holds : V -> Prop` evaluates stored values.
When repair is possible, `repair_choice` selects a healthy reachable candidate.
Otherwise, it selects the original value. The data update is:

```text
repair_state G v w = if w = v then repair_choice G v else w
```

`repair_at` is the graph view of those data. Its health at slot `w` is the
original predicate applied to `repair_state G v w`; edges and reachability
remain unchanged. The specification on values stays fixed.

| Result | Proven property |
| --- | --- |
| `repair_restores` | An available repair makes its target slot healthy. |
| `repair_locality` | Every other slot keeps exactly the same value and health. |
| `healthy_self_stable` | Repair selection and the graph view fix a healthy target. |
| `repair_no_cascade` | Every previously healthy slot remains healthy. |
| `active_independent_of_isolated` | An edge away from the target retains its activity. |

Candidate existence is an explicit hypothesis. Selection uses classical choice.
These are universal properties of the specified local-copy operation; concrete
software repair requires its own implementation and refinement argument.
This file supplies no repair-search or convergence algorithm.

## Scope of elementary helpers

The `Meta` and `Categorical` modules retain their structural laws and accessors.
Transporting correctness across a meta-edge uses a supplied relation-inclusion
proof. Graph-extension helpers in `SelfAssessment` use the same predicate on
unchanged vertex values. Its state-repair section separately requires target
restoration and preservation of the certified core.

`feasible_witness_exists` packages an already supplied numerical LLL assignment.
`lll_budget_feasible_or_infeasible` is excluded middle for numerical budget feasibility;
neither gives a decision procedure. Failure of that sufficient LLL budget
system does not establish semantic impossibility of repair.

`Optimization/ComplementarySlackness.lean` proves pointwise tightness, entry-cost
equality and tight-entry uniqueness under its stated assumptions. Aggregate
primal/dual objectives and strong duality are outside that file's statements.

The whole-library axiom audit checks proof dependencies and declaration coverage.
Matching a comment or a paper's intended theorem remains a separate review task.


## Structural bridges added later on 2026-10-28

In `Core/Meta.lean`, `rr_of_iff_rr_rel_hom` proves correspondence with the core
RR construction. `configs_compatible_of_rel_inclusion` constructs compatibility
when the underlying equivalence grows and abstraction/concretization stay fixed.

Selection now defines a well-defined quotient RR and invariant, proves actual
quotient `pp_valid`, and concludes the shared categorical `pp_morphism` and
`pp_quotient` predicates. Projection requires explicit noncollapse. The
specification-quotient bridge retains its unrestricted edge-or-collapse result
and adds a genuine categorical quotient between certified subgraphs when no
certified source edge collapses.

`Integration.CertificationDependency` indexes the actual certificate list.
Its failing-index set maps exactly to `blocking_set`. At one fixed specification
level, component footprints range over the whole tracked family, including
currently passing certificates. Each update checks its entire affected component
and preserves data outside the footprint. The same
full-family preservation theorem constructs the `valid_repair` contract from
`Certification/SelfAssessment.lean` for the actual certificate predicates and
changed data. Under predicate
locality, a finite checked plan covering every original blocker establishes
full certification.
The theorems require these contracts from each actual intermediate update;
they do not synthesize repairs or infer locality from footprint labels.

`Integration.MoserTardosRepair` now also supplies an actual directed-edge path
under primitive-step compatibility. The canonical resampling graph satisfies
that contract by construction. Recovery states may violate the target, so this
raw path is distinct from a certified PPG walk. Existence of a constant-log path
does not assert positive probability or a random running-time bound for it.

The general MT witness-budget bound uses product-table random initialization.
It is not asserted for every fixed initial state. The separate finite-potential
results give fixed-start bounds or exact expectations under their accessibility
or first-step-equation hypotheses. A supplied log confined to one component
preserves other selected events' truth values; an unrestricted policy is not
assumed to stay in that component automatically.

Numerical feasibility predicates are named `lll_budget_feasible` and
`lll_budget_infeasible`, making their sufficient-criterion scope explicit.
That structural update contained 192 theory modules and 1,842 explicit results;
its extensions added eighteen results to the earlier inventory.


## Finite-read measured instance

`Integration.FiniteReadCertificates` adds a finite comparison language over
rational-valued fields. `Check.reads` traverses the same syntax evaluated by
`Check.eval`; locality is proved by induction. A finite candidate search checks
all certificate positions and equality outside the permitted write footprint.
Its soundness theorem derives `ComponentChecked`, restoration, full certification
and preservation of every previously passing tracked certificate. Its completeness
is relative to that finite candidate bank and those exact checks. It does not
construct an arbitrary code change or assume every input has a passing candidate.

`Integration.LucesCertificateRepair` instantiates it with the runner's actual
local-plan comparisons and five measured boot320 coupling proposals. The eight
positions include four atomic checks, their conjunction, a repeated Monge check,
a signed-generator check and a CSV-digest check. Footprints are derived rather
than asserted. The original independent coupling fails; the fourth proposal
passes the Monge threshold but still fails cycle and sparsity tests; the fifth
passes all positions. The selected change preserves the generator and dataset
fields, and hence the two protected certificates. Duplicate checks remain
separate positions in both this Lean instance and the new indexed PVS bridge.
The legacy PVS predicate-set bridge merges equal predicates and is a separate
construction; no graph isomorphism with that legacy bridge is claimed.

The normative contract is `artifacts/luces/local_plan.json`. The exact observed
binary64 ratios are in `local_plan_kernel_inputs.json`. A frontend file loader,
like `include_str`, emits their ASCII bytes as ordinary Lean literals; it neither
parses JSON nor proves propositions. A bounded pure Lean reader then decodes
these specific files, and kernel proofs identify their checks and rows with the
instance. This reader is not a complete JSON implementation. The audit freshly
elaborates the literal-input owners and records hashes of their inputs, covering
warm Lake caches as well as source changes. No native proof evaluator or additional
axiom is used.

The reader accepts only ASCII strings and integer numbers; it also accepts
leading-zero integers and resolves duplicate object keys to their first value.
The frozen artifacts are strict JSON with unique keys, so those general parser
differences do not affect these concrete decoding proofs. Row decoding validates
field names, row widths and numeric ratios. Metadata hashes and the recorded
selection index are checked by the exporter, rather than by a kernel SHA-256
implementation; the selection theorem independently computes the accepted row.

`tools/export_luces_instance.py --runner-root ../master-controler --check` checks
exact artifacts and their CSV/producer hashes. The runner additionally recomputes
the coupling matrices and extracted features. These are numerical/provenance
checks, not a formal verification of Python, NumPy, POT, the CSV acquisition
process or physical actuation.

`Integration.CertifiedQuotientExample` supplies a concrete noninjective quotient
of the four subsets of `Fin 2`. The two middle vertices merge. Certification
descends by cardinality; strict source edges cannot collapse, and a nonempty
quotient edge is proved. It instantiates the shared categorical `pp_quotient`,
whose contract here is a surjective forward morphism rather than a universal
property for arbitrary categories.

The finite-read integration audit covered 198 modules, 1,876 explicit results and all 5,368
project declarations. The six added modules contribute 34 explicit results; the
remaining additions define the finite reader, file embedding and observed data.

## Repair hazards and observable reduction

The eight modules under `PPGraph/Repair/` add a read/write hazard calculation,
semantic invalidation, checked commits, deterministic observable subalgebras,
finite probabilistic reduction and affine-scheme interpretations.

`Repair.Hazards` requires an action's write-frame proof and read-locality proof.
Its RAW, WAR and WAW tests detect declared footprint interference. Hazard-free
actions commute, and certificates outside an action's affected footprint retain
their truth values under the stated predicate-locality hypothesis. An overlap
alone does not establish that a particular certificate becomes false.
`scopedContract_iff_fullContract` proves that checking the target and the
potentially affected core suffices for the full restoration-and-preservation
contract. The core includes previously passing obligations.

`Repair.SemanticHazards` defines invalidation as a certificate holding before an
operation and failing afterward. Its semantic scope contains exactly those
tracked certificates with an invalidation witness in the specified allowed
domain. This is a possibility over that domain, rather than a failure at every
state. Scope is minimal relative to those predicates, that operation and that
domain, and is contained in the footprint scope when the required frame and
locality proofs hold. Finite classification and exact checked commits require
a `CompleteDomain`; checking an arbitrary sample supplies only the corresponding
sample-relative result. The examples include a proper subset of sampled states
that misses a genuine hazard.

`Repair.ObservableAlgebra` uses Mathlib's `Subalgebra R (S -> R)`. `Stable` means
that every allowed repair's pullback maps the algebra into itself; observable
values may change. `Fixed` means that a particular repair leaves every observable
unchanged. `ObsEq` identifies states with equal retained observables. Stability
preserves this equivalence under finite repair sequences. Computing a decision
from the retained view separately requires its test to factor through those
observables. Observationally equivalent states then give equal decisions after
the same operation sequence; individual decision values need not stay constant.
The least stable hull is characterized by all finite future pullbacks; its definition
does not supply an algorithm that always discovers a small representation.
Disjoint write and observation footprints give a fixed local algebra, while
read closure gives stability under the stated action-locality proofs.

`Repair.ObservableKernel` treats finite rational transition models. Stochastic
expectation is linear and need not preserve multiplication. Full closure of a
projection algebra, `KernelClosed`, is equivalent to equal aggregate transition
masses on each summary fiber, `FiberLocal`, for a surjective summary. The
good-state predicate must also factor through the summary (`GoodLocal`). These
conditions establish the existing `FiniteLumping.Compatible` interface and
transfer stochasticity and survival probabilities under the separate stated
assumptions. An example proves that checking expectation on algebra generators
alone is insufficient.

`Repair.ObservableSchemes` applies affine-spectrum constructions to the same
function algebras and their subalgebras. Restricted repair pullbacks induce
scheme maps commuting with observation; fixed observables give a protected
projection. Concrete states supply evaluation points. The construction does not
identify every spectrum point with a state or turn inequality tests into basic
opens without additional encoding.

These additions are maintained in Lean. Their generic hazard and observable
algebra framework is not asserted to have a corresponding PVS development in
this update. The examples establish mathematical instances and countermodels;
they do not verify a general program-repair synthesizer or a physical controller.

Verification on 2026-10-30 passed the full 4,167-job build without warnings or
errors and the whole-library axiom audit: 206 modules, 2,054 explicit results and
5,835 project declarations. The eight repair modules contribute 178 explicit
results, each with a `#check`. Audited dependencies remain within the standard
`propext`, `Classical.choice`, `Quot.sound` allowlist. The earlier external-kernel
checks remain historical; this update does not claim a new external-checker run.
