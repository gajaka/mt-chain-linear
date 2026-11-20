# MT, probability and repair observables

This theory covers Moser-Tardos resampling, HLS bounds, Shearer criteria,
LLL, probability, repair hazards and stable observable subalgebras. General
results retain their stated hypotheses; their availability alone does not
instantiate them for a particular process.

## Theories

| Location | Contents |
|---|---|
| [MoserTardos/Process/](MT/MoserTardos/Process/) | Product spaces, resampling, initialization and trajectories |
| [MoserTardos/Probability/](MT/MoserTardos/Probability/) | Witness-event laws and independence |
| [MoserTardos/Witness/](MT/MoserTardos/Witness/) and [Counting/](MT/MoserTardos/Counting/) | Witness constructions and resampling counts |
| [MoserTardos/Bounds/](MT/MoserTardos/Bounds/) | Expected work, convergence, termination and drift |
| [HLS/](MT/HLS/) | Witness DAGs, encodings, probabilities and refined budgets |
| [Shearer/](MT/Shearer/) and [LLL/](MT/LLL/) | Local-lemma and dependency-polynomial criteria |
| [Integration/Policy/](MT/Integration/Policy/) | Admissible history-dependent MT and HLS selection policies |
| [Hazards.lean](MT/Repair/Hazards.lean) and [SemanticHazards.lean](MT/Repair/SemanticHazards.lean) | Footprint and semantic invalidation scopes |
| [ObservableAlgebra.lean](MT/Repair/ObservableAlgebra.lean) and [ObservableKernel.lean](MT/Repair/ObservableKernel.lean) | Stable observable subalgebras and probabilistic kernel closure |

[GenericMT.lean](GenericMT.lean) is the entry point. It imports all 44 MT,
63 HLS, 16 Shearer and 3 LLL modules, the four hazard/observable theory
modules, and five policy modules. These 135 roots require 15 further modules
for graph, dependency, drift and finite-kernel definitions: 150 in total.
Every supporting module belongs to their import closure.

## Build and source check

From the project root:

```sh
cd library
lake exe cache get
lake --wfail build GenericMT
python3 -B check.py
```

The workspace pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, sharing the parent's external
package cache. The standard-library source checker verifies the requested
families, every module identity, the exact dependency closure and the import
entry point. [SOURCES.json](SOURCES.json) records both original and current
module hashes; the checker permits only the specified import-path changes.
It writes no receipt. An optional source-checkout comparison is available:

```sh
python3 -B check.py --source /path/to/source-checkout
```

See the [dependency notices](../THIRD_PARTY_NOTICES.md) for provenance and
licensing information.

## Relation to the chain

The [concrete chain](../formal/mt/) has its own finite-kernel definitions
and independently checked Theta(n) proof. Its bounds do not automatically
extend to other processes. A library build checks these theory modules with
Lean; source checks are not mathematical proofs. No fresh Nanoda replay or
blanket second-kernel guarantee is claimed for this workspace.
