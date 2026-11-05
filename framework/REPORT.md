# Original framework restored in mt-chain-linear

The active project is `/Users/gajaka/projects/mt-chain-linear`. The complete
original formal library is physically present at `vendor/ppg-lean` and builds
through the local `framework/` Lake workspace. This completes the requested
source restoration; it does not instantiate that library on Crew.

## Original source

All 228 Git-tracked files from `ppg-lean` commit
`60151677e58704ce856c05a572904d681fd959f6` were copied byte-for-byte from a clean
working tree. The copy includes 208 proof modules, original configuration,
documentation, audit tools, historical reports and the two JSON inputs read
during elaboration. No original file was moved or changed. No build cache or
`.git` directory was copied. The [manifest](SOURCE_MANIFEST.json) records every
file's SHA-256 and size. Historical vendor reports remain historical evidence.

The restored package contains the original:

- MT processes, local resampling, random initialization, witness arguments and
  expected-cost/termination bounds;
- product-space probability and conditional freshness laws, including finite
  resampling and HLS probability modules;
- footprint and exact semantic hazards, with preservation theorems;
- stable observable subalgebras, observation equivalence after operation words,
  probabilistic kernel closure and good-state locality.

[FrameworkAudit.lean](FrameworkAudit.lean) imports `PPGraph.All` and checks
original definitions and nine representative theorem roots across these layers.
The smaller `PPGraph` root alone would only import the graph interface.

## Fresh verification

The copied library and new audit target built with Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All external dependency revisions
match the source and chain project. The first build started without PPGraph
build artifacts; pinned external dependency caches were reused.

The final [attempt-002 receipt](../evidence/framework/attempt-002/RESULT.json)
records:

| Check | Result |
|---|---|
| Original files | 228 exact matches before and after |
| Library modules | 206 implementation modules and 2 import facades |
| Artifact resolution | All 208 modules in the new local build |
| Explicit theorem declarations | 2,054, each with an original explicit `#check` |
| Generated theorem constants | 1,761 |
| All owned declarations inspected | 5,835 |
| Project-owned axioms | 0 |
| Allowed transitive axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Representative theorem roots | 9 present and axiom-checked |
| Build warnings/errors | 0 / 0 |

Both modules embedding JSON were freshly elaborated. Source, configuration,
audit code and manifest inputs were hashed before and after. Lean supplied the
owned declaration inventory; reported axiom output had to cover that exact set.
Module resolution identifies the copied package's artifacts, not the original
checkout's cache. Independent read-only review confirmed the input, log and
artifact bindings.

The [independent copy check](../evidence/framework/copy-check-independent.json)
also compared files directly with the source repository. The chain's existing
[source check](../evidence/framework/source-check-independent.json) passes:
all 34 original Lean files and root Lake configuration are unchanged. Its
`ppgraph_package_present: false` field concerns the unchanged root workspace;
the additional framework workspace has the local PPGraph dependency. The
original chain build also passed.

Attempt 001 built and audited successfully. Attempt 002 adds input binding,
root-output and module-resolution checks. Its predecessor's driver and receipt
are retained. No historical receipt was replaced.

This is a Lean build and whole-library **reported-axiom audit**, not a new
Nanoda run or independent traversal of every raw proof body. Earlier chain
Nanoda evidence remains scoped to its recorded roots.

## Organization and replay

```text
mt-chain-linear/
  formal/mt/                 original chain and Theta(n) proofs
  vendor/ppg-lean/            complete unchanged original generic library
  framework/                 local Lake integration, audit and verifier
  evidence/framework/        fresh build and audit evidence
```

This is one Git project with two build scopes. Their separation preserves the
original extraction/migration manifests and the independent Theta(n) import
closure.

```sh
# From the mt-chain-linear root:
make check

# Framework alone; writes a new evidence attempt:
python3 framework/check.py

# Read-only comparison with the original checkout:
python3 framework/verify_copy.py --compare-source ../ppg-lean
```

Kiro reproductions remain in
`../ppg-proof-repair/experiments/kiro-crew-comparison`. They were not moved,
extended or retroactively certified. An application must still establish its
MT law, repair footprints, semantic hazard, stable observable and code
correspondence. The chain's Theta(n) bound does not transfer automatically.
