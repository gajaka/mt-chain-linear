# Provenance and dependency notices

The project's code and documentation are licensed under the
[MIT License](LICENSE), copyright 2026 Dragan Stosic. External dependencies
and any third-party source excerpts retain their own licenses and notices.

`SOURCE_MANIFEST.json` and `MODULE_MIGRATION.json` identify the finite-chain
sources and the permitted source-header adaptations. Author headers and the
source notices of the accounting and barrier supplement are preserved.

`library/` contains the MT, HLS, Shearer, LLL, probability, hazard and
observable-algebra theories at source revision
`60151677e58704ce856c05a572904d681fd959f6`, with their required definitions.
[library/SOURCES.json](library/SOURCES.json) records source identities and
hashes for both original and current modules. Author headers, mathematical
declarations and proof bodies are preserved. The import prefix is `MT` in this
workspace; only import paths differ from the recorded source bytes.

Mathlib is an external dependency, pinned in `lakefile.lean` and
`lake-manifest.json`, and is distributed under the Apache License 2.0. Its
[upstream license at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/LICENSE)
and source notices remain applicable. Lean and transitive dependencies retain
their respective upstream licenses and notices; dependency downloads and caches
are not relicensed by this project.

Nanoda, when used for independent checking, is an external tool, not a library
dependency or a bundled part of these proof sources. Its license and the exact
executable/revision used must be retained in the corresponding verification
record. Nanoda is not required by the MT library build.

The research references identify prior mathematical work, not incorporated
third-party implementation code. Formal verification, provenance, permission to
redistribute, and scientific priority are separate questions.
