# Certificate existence and restricted-budget separation

## Outcome

Both the coordinate-separable and larger one-bridge classes have explicit
certificates for every `n >= 2`. Every coordinate-separable certificate has an
exponential normalized initial budget. In particular, this class admits no
O(n^2)-budget family. The larger one-bridge class has a quadratic lower bound;
quadratic attainment is open.

The same initialized process still satisfies `n/18 <= E[T_n] <= 1054*n`.
This is a separation between analysis certificates and actual expected
resampling count. No algorithm was changed or accelerated.

## Exact proof obligations

The [README](README.md) defines both classes, including the global reset at
Good states. Neither class is assumed inhabited in the combined results.

| Declaration | Statement |
| --- | --- |
| `PotentialSeparation.Construction.certificate` | Explicit `DriftCertificate n` from `2 <= n`, with delta 1 |
| `PotentialSeparation.Construction.pointwise_drift` | Every active raw state has expected potential drop at least 1 under its selected full-footprint redraw |
| `PotentialSeparation.Construction.initial_budget_upper` | Constructed initial budget is at most `3*9^(n-2)+1` |
| `PotentialSeparation.Exponential.certificate_budget_exponential_lower` | For any certificate and `2*k+4 <= n`, budget is at least `(5^(k+1)-3)/36` |
| `PotentialSeparation.Exponential.certificate_budget_floor_lower` | For `n >= 4`, budget is at least `(5^(floor((n-4)/2)+1)-3)/36` |
| `NeighborSeparation.Embedding.certificate` | Transfers each separable certificate into the one-bridge class |
| `NeighborSeparation.Embedding.certificate_budget_eq` | The embedding preserves budget exactly |
| `CertificateStudy.nonvacuous_separable_separation` | Actual existence, exponential class lower bound and linear process bounds in one conjunction |
| `CertificateStudy.nonvacuous_neighbor_separation` | Actual existence, quadratic larger-class lower bound and linear process bounds in one conjunction |

The exact finite-n inequalities are formalized. Their exponential-versus-linear
growth interpretation is elementary; no new Lean declaration for an optimized
class minimum or optimal exponential base is claimed. The quadratic
inequalities remain valid and sometimes have better small-n constants.

## Why this is not a vacuous lower bound

`CertificateConstruction.lean` supplies concrete threshold and label tables,
proves their nonnegativity and every raw pointwise drift obligation, and builds
the structure. It does not use an existential premise, a runtime bound, a
numerical feasibility result or the failure of another proof search to establish
existence. Its mean is computed under the original product distribution.

`NeighborEmbedding.lean` proves equality of raw scores, stopped potentials and
budgets before constructing the larger-class certificate. Thus both lower-bound
theorems have actual objects to which they apply for all claimed lengths.

The certificate structures specify the required properties without asserting
that an inhabitant exists. The explicit construction discharges that separate
existence obligation for every claimed length.

## Independent verification

The recorded strict study build and independent replay passed:

| Check | Recorded result |
| --- | --- |
| Study mathematical build from an empty local build directory | 18 modules, 0 warnings, 0 errors, 19.976 s |
| Source closure | 49 local modules: 18 research + 31 root-package modules |
| Source identity check | Mathematical sources and reference snapshots match their recorded hashes |
| Independent statement/binder/axiom audit | 9 selected roots, actual proof closure 17,732 declarations |
| Nanoda replay | 18,183 expanded declarations, 5.191 s, PASS |
| Imported artifacts bound by hash | 5,552 modules, 33,312 artifacts |
| Allowed transitive axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Saved-evidence read-only check | PASS |

The private proof environment is loaded explicitly, so theorem bodies remain
available to the axiom audit. Expected theorem types are independently stated
by the auditor. The proof closure does not depend on the general theory
library.

The selected roots are listed in
[attempt-001/RESULT.json](evidence/attempt-001/RESULT.json). The root set covers
construction, upper budget, both exponential lower-bound forms, embedding and
both combined separations. This is not a claim of an independent replay of
every declaration in the imported source modules. A source-level proof check
also does not verify an external implementation of the chain.

[VERIFICATION.json](evidence/VERIFICATION.json) binds the source receipt,
strict build and replay. The root package's Theta(n) result has a separate
[audit receipt](../../evidence/attempt-003/RESULT.json).

## Build and verification inputs

The study has its own Lake manifest and local build directory. It imports the
root package's concrete-chain core and shares the pinned external dependency
cache. Its 18 mathematical modules and verification tools are identified by
[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json); the read-only source checker also
validates the recorded reference snapshots.

The successful 18-module build is recorded in
[clean-build-001/RESULT.json](evidence/clean-build-001/RESULT.json). Earlier
build logs are retained as historical evidence and are not additional proof
results. A reproducible build requires only this checkout and its pinned
dependencies.

## What remains open

- An O(n^2) upper certificate for the larger one-bridge class is not established.
  Its nonemptiness and quadratic lower bound now both hold, but do not imply
  quadratic attainment. Its available explicit upper bound is exponential.
- The exact optimal exponential rate for the narrower class is not identified.
- Arbitrary nonseparable raw pointwise potentials, wider bridge interactions,
  other drift conditions, alternative initializations and repair rules are not
  excluded by the new obstruction.
- The linear process theorem and the certificate obstruction do not establish
  wall-clock speedup or compiler-time complexity.
- Scientific priority remains unestablished. The primary-source comparison and
  proposed questions for a reviewer are in [LITERATURE.md](LITERATURE.md).
