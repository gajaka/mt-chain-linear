# Original generic MT formalism from ppg-lean

This workspace contains the original generic Moser-Tardos formalism, its
probability theory, and the repair-hazard and observable-algebra modules.
The 63 copied Lean files are byte-identical to `ppg-lean` commit
`60151677e58704ce856c05a572904d681fd959f6`.

All 44 original `PPGraph/MoserTardos/` modules are included, together with
their dependencies and four repair roots. The source selection excludes
unrelated applications, images, old reports and build artifacts.

| Location | Contents |
|---|---|
| [Process/Basic.lean](PPGraph/MoserTardos/Process/Basic.lean) | Product variable spaces, generic state, resampling and footprint dependence |
| [Process/Process.lean](PPGraph/MoserTardos/Process/Process.lean) | Generic MT processes, trajectories and event selection |
| [Probability/](PPGraph/MoserTardos/Probability/) | Witness-event probabilities, initialization and independence |
| [Witness/](PPGraph/MoserTardos/Witness/) and [Counting/](PPGraph/MoserTardos/Counting/) | Witness constructions and resampling counts |
| [Bounds/](PPGraph/MoserTardos/Bounds/) | Expected work, convergence, termination and drift results under their hypotheses |
| [Repair/Hazards.lean](PPGraph/Repair/Hazards.lean) and [SemanticHazards.lean](PPGraph/Repair/SemanticHazards.lean) | Footprint and semantic invalidation scopes |
| [Repair/ObservableAlgebra.lean](PPGraph/Repair/ObservableAlgebra.lean) and [ObservableKernel.lean](PPGraph/Repair/ObservableKernel.lean) | Stable observable subalgebras and probabilistic kernel closure |

[GenericMT.lean](GenericMT.lean) imports the selected family.
[SOURCES.json](SOURCES.json) identifies every copied source and its SHA-256.
Original module paths, mathematical bodies and author headers are preserved.
See the parent [dependency notices](../THIRD_PARTY_NOTICES.md); this copy does
not assign a new blanket license to the original material.

## Build and source check

From the project root:

```sh
cd library
lake exe cache get
lake --wfail build GenericMT
python3 -B check.py
```

This separate Lake workspace pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. It shares the parent's external
package cache. The source check uses only Python's standard library, writes
no receipt, and verifies the copied inventory, hashes and import closure.
Optionally compare directly with the original checkout:

```sh
python3 -B check.py --source /path/to/ppg-lean
```

## Relation to the concrete chain

The generic library is available here as the original mathematical framework.
The concrete chain in the parent's `formal/mt/` has its own finite-kernel
definitions and an independently checked Theta(n) proof. That proof does not
import this workspace. Copying and building the generic library does not
instantiate its convergence hypotheses for the chain or another program.

A successful build checks these modules with Lean; the source checker proves
no mathematical theorem. No fresh Nanoda replay or transfer of historical
second-kernel results is claimed for this new workspace.
