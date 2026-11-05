# Provenance and dependency notices

This project extracts finite-chain proof sources from `../ppg-proof-repair`.
`SOURCE_MANIFEST.json` records the original paths, copied-file hashes and any
explicit wrapper or audit adaptations. Copied source headers are preserved.
The separate accounting/barrier supplement retains its original provenance.

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
