# Verification tools and reproduction

The project pins Lean `leanprover/lean4:v4.35.0` and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The nine dependency packages are
listed in `lake-manifest.json`. A dependency
used only by Lake tooling, such as Cli, need not have a Lean library cache.

The independent checker command accepts `--nanoda PATH` (or `NANODA_BIN`).
Its binary hash pins identify the checked tool builds. They do not imply
identical binaries on every operating system.

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

[TOOL_PROVENANCE.json](tooling/TOOL_PROVENANCE.json) records the source, local
patch, binary identity and build environment. Proof replay checks that
binary's identity; it does not rebuild or test the Rust checker.

## Fresh and saved-evidence checks

After the project has been built, run:

```sh
python3 -B scripts/independent.py --nanoda /path/to/nanoda_bin --attempt attempt-004
```

Each fresh attempt gets a separate directory under `evidence/`. Raw exports
go under `evidence/exports/` and are excluded from Git. The script creates an
explicit fresh module path from this project's own build and dependency
copies. It checks that the thirty raw chain modules and their facade resolve
under this project's build cache, without importing a wrapper proof of the
result being audited.

It independently audits the exact statements and binders of nine selected
roots, traverses their actual proof dependencies, exports them, and runs
Nanoda with only `propext`, `Classical.choice` and `Quot.sound` permitted.
This checks those roots and their proof closure; it does not check every
assertion in every source file with the second kernel.

Attempt 003 checks the current chain sources. Use an unused attempt name for
a fresh replay. The checked binary hashes are specific to the recorded
macOS tool builds; another platform requires reviewed tool pins and fresh
verification records.

To verify the retained hashes and logs without executing Lean or Nanoda:

```sh
python3 -B scripts/independent.py --verify --attempt attempt-003
```

This requires the recorded local artifacts, including the ignored export.
Published source and compact receipts alone do not contain every binary or
raw proof export required for that local saved-evidence check.

Absolute paths in saved receipts and logs identify locations on the machine
used for the recorded check. They are not installation requirements. Fresh
replays use the current checkout and a new attempt directory; verifying a
historical receipt can require its recorded artifacts and path bindings.
The original receipts and logs are retained without rewriting those paths.

The source validator checks [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) and
[MODULE_MIGRATION.json](MODULE_MIGRATION.json). It verifies the reference
source bytes, replays the permitted module-header transformation, and checks
the current import boundary. The audit loads a second environment with full
private proof data; ordinary module
imports alone can omit transitive theorem bodies. The audit process uses an
8 GiB memory cap for these two environments, while the checked roots, exact
type checks and three-axiom allowlist stay unchanged.

`scripts/verify.py` also refuses to overwrite a receipt. Its default output is
`evidence/migration-source-verification.json`; use `--output` with an unused path
for a subsequent source check. The independent runner invokes the same validation
without writing or overwriting a source receipt.

Earlier receipts apply only to the source versions and paths recorded in
their own inputs. They do not replace the current-source check in attempt 003.

## Historical verification records

Earlier attempts, build logs and diagnostic probes are available in
[the recorded evidence revision](https://github.com/gajaka/mt-chain-linear/tree/14e8b2ccba6dfaf78b692855b2629a02bf258cd6/evidence),
including [attempt 002](https://github.com/gajaka/mt-chain-linear/tree/14e8b2ccba6dfaf78b692855b2629a02bf258cd6/evidence/attempt-002)
and the [module-audit diagnostics](https://github.com/gajaka/mt-chain-linear/tree/14e8b2ccba6dfaf78b692855b2629a02bf258cd6/evidence/module-audit-diagnostics).
The early build paths `evidence/lean-build-001/` through `004/` also resolve
at that revision. Historical paths in the unchanged aggregate receipt identify
those records. The current chain verification uses `evidence/attempt-003/`
and `evidence/lean-build-005/`, which remain in this checkout.
