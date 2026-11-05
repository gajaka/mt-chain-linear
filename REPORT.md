# Standalone extraction verification report

The existing initialized MT-chain analysis builds and passes a fresh independent
proof replay in this separate project. No PPGraph library or old project build
path is needed. This extraction adds packaging and verification evidence; it
adds no new mathematical runtime theorem or claim of novelty.

## Source preservation

- 30 modules form the exact local import closure of `LinearAsymptotics`.
- `Accounting` and `Barrier` are two additional unchanged paper supplements.
- All 32 copies match their original SHA-256 values.
- The adapted `TightnessResults` removes the PPG import and three PPG corollaries.
- The adapted audit checks nine raw-process roots instead of twelve mixed roots.
- The source comparison checked 81 original Lean sources/configurations unchanged.

[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) records exact identities and
adaptations. The aggregate binds the preserved
[extraction source receipt](evidence/extraction-source-verification.json).
[source-verification.json](evidence/source-verification.json) is a separate,
explicitly refreshable derived check, not a historical proof receipt.

## Fresh checks

| Check | Result |
| --- | --- |
| Clean default Lake build | PASS, 34 local modules, 44.151 seconds |
| Actual theorem types, binders and proof bodies | PASS, nine roots |
| Raw transitive kernel closure | 17,228 declarations; only three standard axioms |
| Fresh Nanoda replay | PASS, 17,688 expanded declarations |
| Loaded module boundary | 5,534 modules; no PPG imports or old local object paths |

The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
Nanoda checked the nine selected roots and their exported proof dependencies,
not every assertion in all 34 local modules. The raw-kernel and expanded-export
inventories use different counting conventions and are recorded separately.
The checker itself took about 3.21 seconds; the complete independent pipeline,
including audit, export and file-identity checks, took about 40.45 seconds.
External dependency caches were reused. No old project `.olean` was copied.

The clean build emitted 23 module-migration warnings because the unchanged
legacy proof sources import module-system Mathlib modules. The initial
`--wfail` build rejected these warnings; both the failure and the successful
normal builds are retained. No proof source was rewritten to remove warnings.

Independent attempt 001 stopped before any prover/exporter/checker: the runner
incorrectly demanded a library cache for the tool-only Cli dependency. Its
failure and original runner are retained. The correction validates package
locations and requires every actually imported artifact. Fresh attempt 002
then passed; it did not overwrite attempt 001.

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
