# MT and probability theory

This workspace contains the complete mathematical library: 208 Lean modules,
including both entry points and 206 implementation modules. Its theories cover
Moser-Tardos resampling, probability, HLS bounds, Shearer criteria, dependency
structures, repair hazards, certification and stable observable algebras.

## Mathematical modules

| Location | Contents |
|---|---|
| [MoserTardos/Process/](PPGraph/MoserTardos/Process/) | Product variable spaces, state, resampling, initialization and trajectories |
| [MoserTardos/Probability/](PPGraph/MoserTardos/Probability/) | Witness-event probabilities and independence |
| [MoserTardos/Witness/](PPGraph/MoserTardos/Witness/) and [Counting/](PPGraph/MoserTardos/Counting/) | Witness constructions and resampling counts |
| [MoserTardos/Bounds/](PPGraph/MoserTardos/Bounds/) | Expected work, convergence, termination and drift under stated hypotheses |
| [HLS/](PPGraph/HLS/) | Witness DAGs, encoding, probability and refined budget results |
| [Shearer/](PPGraph/Shearer/) and [LLL/](PPGraph/LLL/) | Dependency-polynomial criteria, slack, probability and expected-work results |
| [Finite/](PPGraph/Finite/) | Finite resampling laws, potentials, drift and lumping |
| [Repair/](PPGraph/Repair/) | Footprint and semantic hazards, stable observable algebras and kernel closure |
| [Integration/](PPGraph/Integration/) | Connections between process, repair, policy and certification theories |
| [Core/](PPGraph/Core/), [Dependency/](PPGraph/Dependency/), [Certification/](PPGraph/Certification/) and [Decision/](PPGraph/Decision/) | Supporting graph, dependency, certificate and decision definitions |

All 44 Moser-Tardos, 63 HLS and 16 Shearer modules are present.
[PPGraph/All.lean](PPGraph/All.lean) exposes every implementation module;
[GenericMT.lean](GenericMT.lean) imports both library entry points.
Individual modules can also be imported separately.

## Build and check

From the project root:

```sh
cd library
lake exe cache get
lake --wfail build GenericMT
python3 -B check.py
```

The workspace pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and shares the parent's external
package cache. `check.py` uses only Python's standard library and writes no
receipt. It verifies all 208 module identities, complete import coverage and
the two small JSON inputs required while elaborating the integration examples.
Those inputs are mathematical fixtures, not a log collection or dataset.
[SOURCES.json](SOURCES.json) records source identities and SHA-256 values;
[dependency notices](../THIRD_PARTY_NOTICES.md) state the applicable provenance
and licensing boundaries.

An optional comparison against the identified source checkout is available:

```sh
python3 -B check.py --source /path/to/source-checkout
```

## Relation to the concrete chain

The concrete chain in [formal/mt/](../formal/mt/) has its own finite-kernel
definitions and independently checked Theta(n) proof. That proof does not
import this workspace. Availability of the generic theories does not by itself
instantiate their convergence hypotheses for that chain or another program.

A successful build checks these modules with Lean. The source-identity checker
is not a mathematical proof. No fresh Nanoda replay or blanket transfer of
historical second-kernel results is claimed for this workspace.
