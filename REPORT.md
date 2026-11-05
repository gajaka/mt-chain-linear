# Standalone extraction and module migration verification report

The existing initialized MT-chain analysis builds and passes a fresh independent
proof replay in this separate project. No PPGraph library or old project build
path is needed. This extraction adds packaging and verification evidence; it
adds no new mathematical runtime theorem or claim of novelty.

## Source preservation and module migration

- 30 modules form the exact local import closure of `LinearAsymptotics`.
- `Accounting` and `Barrier` are two additional paper supplements.
- All 32 original extraction copies are preserved with their original SHA-256 values.
- The adapted `TightnessResults` removes the PPG import and three PPG corollaries.
- The adapted audit checks nine raw-process roots instead of twelve mixed roots.
- The source comparison checked 81 original Lean sources/configurations unchanged.

[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) remains the unchanged extraction
record. The pre-migration sources, tooling and aggregate are preserved under
`provenance/module-migration/before/`; the earlier evidence directories are
untouched. [MODULE_MIGRATION.json](MODULE_MIGRATION.json) records current hashes
and the exact permitted transformations. The source validator checks both stages.

All 33 mathematical modules now use `module`, `public import` and
`@[expose] public section`. Their mathematical source bodies are unchanged.
The separate audit module also uses the module system, with an explicit
full-private inspection environment. This keeps every transitive theorem body
available for the original strict axiom traversal. Its module inventory includes
both the quotation environment and that inspection environment.

`scripts/verify.py` writes `evidence/migration-source-verification.json` by default.
It does not overwrite either original source receipt. The package explicitly
requires the module system; no warning category or linter is disabled.

Five [negative controls](evidence/module-migration-validator-controls.json)
were rejected in temporary copies, including a changed mathematical body with
an updated hash, an injected import and substituted or incomplete inventories.
The controls left all 85 bound current/archive/tooling inputs unchanged.

## Fresh checks

| Check | Result |
| --- | --- |
| Clean `lake --wfail build` | PASS, 34 local modules, zero warnings/errors, 36.954 seconds |
| Actual theorem types, binders and proof bodies | PASS, nine roots |
| Raw transitive kernel closure | 17,247 declarations; only three standard axioms |
| Fresh Nanoda replay | PASS, 17,707 expanded declarations |
| Loaded module boundary | 5,534 modules; no PPG imports or old local object paths |

The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
Nanoda checked the nine selected roots and their exported proof dependencies,
not every assertion in all 34 local modules. The raw-kernel and expanded-export
inventories use different counting conventions and are recorded separately.
The checker itself took about 3.29 seconds; the complete independent pipeline,
including audit, export and file-identity checks, took about 35.17 seconds.
External dependency caches were reused. No old project `.olean` was copied.

The [root comparison](evidence/module-migration-root-comparison.json) confirms
identical type ASTs and axiom lists for all nine selected theorems. Two compiled
proof terms now reference compiler-generated helpers with private names. Their
source proof bodies are unchanged; the new compiled terms and dependencies
were checked afresh. The declaration counts above describe this new export,
not the smaller historical one.

## Earlier failures and their fixes

The original clean build emitted 23 warnings because legacy proof sources
imported module-system Mathlib modules. The initial `--wfail` build rejected
them. The original failed and successful builds remain in attempts 001-003.
Build 004 verifies the 33 migrated mathematical modules with `--wfail`, zero
warnings and zero errors.

The first audit migration probe changed only its header. It correctly failed:
transitive theorem bodies hidden by module visibility appeared as axioms.
Loading full private proof data resolves that visibility problem without
enlarging the axiom allowlist. A second probe reached the old 4 GiB memory cap;
the same audit passed with an 8 GiB cap. These diagnostic sources, commands
and logs are retained in `evidence/module-audit-diagnostics/`.

Independent attempt 001 stopped before any prover/exporter/checker: the runner
incorrectly demanded a library cache for the tool-only Cli dependency. Its
failure and original runner are retained. The correction validates package
locations and requires every actually imported artifact. Fresh attempt 002
then passed; it did not overwrite attempt 001. Attempt 002 is historical after
the module migration: its original active-source bindings intentionally no
longer match the changed working tree. Current verification uses attempt 003,
whose saved-evidence check also passes.

[VERIFICATION.json](evidence/VERIFICATION.json) binds the build, source, audit,
module inventory and checker receipts. [TOOLING.md](TOOLING.md) explains the
external tools and the recorded resource-only Nanoda stack-size patch.
Raw proof exports and compiled caches remain local and are excluded from Git.
Saved-evidence verification requires those artifacts and their recorded paths;
a new checkout should build and create its own unused verification attempt.

## Meaning of the result

For every `n >= 2`, the registered product-initialized, least-failed,
full-local-redraw process satisfies:

```text
n/18 <= E[T_n] <= 1054*n
E[T_n] = Theta(n)
E[I_n] <= 2108*n
```

Initialization is excluded, and these are ideal resampling-operation counts.
The lower/Theta proof retains its current use of quadratic finiteness. The
public profile-subalgebra, semantic-scope and certified-graph modules stay in
the original project; this package does not claim their theorems were extracted.
The Shearer classification in the README is an exact arithmetic comparison,
not a new Lean/Nanoda theorem from this extraction. Scientific novelty, a
first-MT-formalization claim and automatic transfer to practical repair remain
unestablished. The old project and its historical receipts were not edited.
