# Lean 4.37.0-rc1 migration

Migration date: 20 November 2026. Branch: `upgrade/lean-4.37.0-rc1`.
Baseline commit: `bb903c9b301a01e136842d7b72719d97d0625745`.

All four active workspaces use Lean `leanprover/lean4:v4.37.0-rc1` and Mathlib
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`:

- The concrete chain and independent theorem auditor.
- The selected 150-module MT/HLS/Shearer/LLL/hazard/observable library.
- The 18-module certificate-existence study.
- The biased-resampling study.

This is a release candidate. Changing a toolchain does not establish a new
mathematical result or extend an existing theorem to a different process.

## Preserved provenance

`SOURCE_MANIFEST.json`, `MODULE_MIGRATION.json`, the generic library's
`SOURCES.json`, certificate-study manifests and earlier scientific evidence
retain their original bytes. A new versioned
[compatibility record](../provenance/lean-4.37.0-rc1/MIGRATION.json) binds the
complete baseline inventory, before/current hashes and exact replacement
ranges. Its baseline inventory has a fixed digest in the validator.

Legacy source checks validate the old module adaptation using the retained
before bytes, then separately verify the exact active edits and current import
closure. New independent runs bind the compatibility record and validator as
inputs. The original extraction is not relabeled as a new kernel check.

Compatibility fixes include generalized infinite sums, finite-set API names,
explicit set arguments in indicator proofs and the renamed strong-induction
case. The mathematical source inventory and requested theory scope do not grow.

## Reproduction

```sh
lake exe cache get
make check
```

`make check` builds every active workspace with warnings as errors, checks the
new migration admission controls and retained source identities, and replays
the saved exact rational window/barrier checks. It does not run Nanoda.

The biased-study verifier also creates a fresh local attempt and rejects its
four invalid-proof/assumption controls. Its active `RESULT.json` pointer is
updated normally, with the previous bytes preserved in the migration's
`before/` inventory. Historical attempts and their outcomes are not overwritten.

Fresh selected-root checks use the current Lean/exporter hash profile while
retaining the existing patched Nanoda binary:

```sh
python3 -B scripts/independent.py --nanoda /path/to/nanoda_bin --attempt UNUSED_ATTEMPT
python3 -B research/certificate-existence/scripts/independent.py \
  --nanoda /path/to/nanoda_bin --attempt UNUSED_ATTEMPT
```

These check nine roots per study and their proof closures, not every theorem
in the repository. New receipts use unused directories. The biased study's
Lean audit is a separate check and does not inherit a Nanoda replay.

Actual migration outcomes are recorded in `tooling/LEAN_4_37_RESULT.json`.
