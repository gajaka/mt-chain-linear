# Verification tools and provenance

The project pins Lean `leanprover/lean4:v4.35.0` and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The nine dependency packages are
listed in `lake-manifest.json`; there is no PPGraph dependency. A dependency
used only by Lake tooling, such as Cli, need not have a Lean library cache.

The independent checker command accepts `--nanoda PATH` (or `NANODA_BIN`).
It does not depend on the location of the earlier research projects. Its binary
hash pins identify the locally checked tool builds; they are not claims that
every build on every operating system has identical bytes.

| Tool | Version or source | SHA-256 of selected binary |
|---|---|---|
| Lean | Lean 4.35.0 | `d1d9c26a539f54fe839d2aa7760bf1ac1dd76a30b26e2c9684bebf2900038fcf` |
| leanexport | Lean 4.35.0 toolchain; NDJSON format 3.1.0 | `01327b83d6a69dbc84fa04fd671c61068b2f074e51d1bf607bf6a6b9aed5339e` |
| Nanoda | nanoda_lib 0.4.24, revision below, with stack-size patch | `4f2264a0c987e94c4a654768a90ddb92369014578ecafba3287020bec0f4d439` |

## Nanoda source and the local resource patch

Nanoda is the independent Lean type checker from
[ammkrn/nanoda_lib](https://github.com/ammkrn/nanoda_lib). The selected binary
was built from upstream revision
[`f67473ba5f9397266f89c7852082c9c914b5d219`](https://github.com/ammkrn/nanoda_lib/commit/f67473ba5f9397266f89c7852082c9c914b5d219).
The source package declares version `0.4.24` and the Apache-2.0 license.

The only local tracked source change increases `STACK_SIZE` in `src/lib.rs`
from 16 MiB to 256 MiB. The exact patch is preserved in
[nanoda-stack-size.patch](tooling/nanoda-stack-size.patch). This is the checker's
internal thread-stack allocation; the standalone runner does not raise the
parent process stack limit or use a `preexec_fn` stack modification.
The patch uses zero lines of context; apply it with `git apply --unidiff-zero`.

The selected upstream revision already contains the fixes associated with
[upstream PR 45](https://github.com/ammkrn/nanoda_lib/pull/45). The local patch
does not change type-checking rules, permitted axioms or export parsing.

The earlier build record reports Rust
`rustc 1.99.1 (58cf8f9c3 2026-10-13)`, SDK `MacOSX26.5.sdk`, a successful
release build, and a successful test run. Those are historical tool-build
records. This extraction checks the selected binary identity and uses it for
a fresh proof replay; it does not claim a new Rust rebuild or test run.
[TOOL_PROVENANCE.json](tooling/TOOL_PROVENANCE.json) records the source, local
patch, binary and historical-record identities.

## Fresh and saved-evidence checks

After the project has been built, run:

```sh
python3 -B scripts/independent.py --nanoda /path/to/nanoda_bin --attempt attempt-003
```

Each fresh attempt gets a separate directory under `evidence/`. Raw exports
go under `evidence/exports/` and are excluded from Git. The script creates an
explicit fresh module path from this project's own build and dependency
copies. It rejects PPG/profile wrapper imports and checks that the thirty raw
modules and raw facade resolve under this project's build cache.

It independently audits the exact statements and binders of nine selected
roots, traverses their actual proof dependencies, exports them, and runs
Nanoda with only `propext`, `Classical.choice` and `Quot.sound` permitted.
This checks those roots and their proof closure; it does not check every
assertion in every source file with the second kernel.

Attempt 002 is the completed replay retained here. Attempt 001 failed during
preflight because the runner incorrectly required a library cache for the
unused Cli tool dependency; no prover/exporter/checker was launched in that
attempt. The original runner and failure are retained. Use an unused attempt
name for a fresh replay. The checked binary hashes are specific to the recorded
macOS tool builds; another platform needs an explicitly reviewed tool-pin
revision and its own fresh receipts.

To verify the retained hashes and logs without executing Lean or Nanoda:

```sh
python3 -B scripts/independent.py --verify --attempt attempt-002
```

This requires the recorded local artifacts, including the ignored export.
Published source and compact receipts alone do not contain every binary or
raw proof export required for that local saved-evidence check.
