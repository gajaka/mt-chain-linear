# Provenance and dependency notices

This project extracts finite-chain proof sources from `../ppg-proof-repair`.
`SOURCE_MANIFEST.json` records the original paths, copied-file hashes and any
explicit wrapper or audit adaptations. Copied source headers are preserved.
The separate accounting/barrier supplement retains its original provenance.

`library/` additionally contains selected original sources from `ppg-lean`
revision `60151677e58704ce856c05a572904d681fd959f6`: all original MT modules
and the dependency closure for the included hazard and observable-algebra
theories. [library/SOURCES.json](library/SOURCES.json) records the exact copied
files and hashes. Original author headers and source bytes are preserved;
the copy does not introduce a new blanket license for that material.

The extraction does not introduce a blanket license for copied project material
whose license has not been specified. A public release should state the license
chosen by the relevant rights holders for that material separately.

Mathlib is an external dependency, pinned in `lakefile.lean` and
`lake-manifest.json`, and is distributed under the Apache License 2.0. Its
[upstream license at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/LICENSE)
and source notices remain applicable. Lean and transitive dependencies retain
their respective upstream licenses and notices; dependency downloads and caches
are not relicensed by this project.

Nanoda, when used for independent checking, is an external tool, not a library
dependency or a bundled part of these proof sources. Its license and the exact
executable/revision used must be retained in the corresponding verification
record. No PPGraph library is required by this standalone extraction.

The research references identify prior mathematical work, not incorporated
third-party implementation code. Formal verification, provenance, permission to
redistribute, and scientific priority are separate questions.
