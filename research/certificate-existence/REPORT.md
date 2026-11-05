# Certificate existence and restricted-budget separation

## Outcome

The missing inhabitedness obligation is closed constructively for every
`n >= 2`, for both the coordinate-separable and larger one-bridge classes.
Moreover, the coordinate-separable class has an exponential lower budget,
stronger asymptotically than the previously proved quadratic obstruction.
It cannot have the suggested O(n^2) budget family.

The same initialized process still satisfies `n/18 <= E[T_n] <= 1054*n`.
This is a separation between analysis certificates and actual expected
resampling count. No algorithm was changed or accelerated.

## Exact proof obligations

The [README](README.md) defines both classes, including the global reset at
Good states. Neither class is assumed inhabited in the new combined results.

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
class minimum or optimal exponential base is claimed. The older quadratic
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

The old comments saying that the *definition alone* does not assert all-length
existence were deliberately retained in the extracted files. That statement
remains true; the new construction now discharges the separate obligation.
Original documents and proof sources were not retrospectively rewritten.

## Independent verification

The final strict child build and the fresh two-checker replay passed:

| Check | Recorded result |
| --- | --- |
| Fresh child mathematical build | 18 modules, 0 warnings, 0 errors, 19.976 s |
| Source closure | 49 local modules: 18 research + 31 parent |
| Optional original-source comparison | All 14 copied mathematical sources match their archived originals |
| Independent statement/binder/axiom audit | 9 selected roots, actual proof closure 17,732 declarations |
| Fresh Nanoda replay | 18,183 expanded declarations, 5.191 s, PASS |
| Imported artifacts bound by hash | 5,552 modules, 33,312 artifacts |
| Allowed transitive axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Saved-evidence read-only check | PASS |

The private proof environment is loaded explicitly, so the Lean module system
cannot hide proof bodies from the axiom audit. Expected theorem types are
independently stated by the auditor. The checker uses the original stack limits;
no stack-limit workaround was applied. There are no PPG imports.

The selected roots are listed in
[attempt-001/RESULT.json](evidence/attempt-001/RESULT.json). The root set covers
construction, upper budget, both exponential lower-bound forms, embedding and
both combined separations. This is not a claim of an independent replay of
every declaration in the imported source modules. A source-level proof check
also does not verify an external implementation of the chain.

[VERIFICATION.json](evidence/VERIFICATION.json) binds the source receipt, clean
build and fresh replay. The larger parent Theta(n) audit is still its separate
`evidence/attempt-003`; this work does not replace that historical receipt.

## Extraction and failed checks

Fourteen old modules were copied, never moved. Byte-identical originals remain
in `provenance/original/`. Active copies received the recorded module headers.
`SeparableWitness.lean` additionally required removal of inherited unused
binders/simp arguments and redundant tactic combinators. Mathematical statement
types and binder order were preserved; the exact cleanup diff is recorded in
[COPY_ADAPTATIONS.json](COPY_ADAPTATIONS.json). No linter was disabled.

The initial strict import build failed on those inherited warnings and is
preserved in `evidence/import-build-001`. The corrected 14-module lint build is
in `evidence/lint-build-001`. The final 18-module fresh build is in
`evidence/clean-build-001`. All new proof sources and audit tooling were sealed
in the manifest before fresh independent verification; they were not modified
after that attempt began.

The child has its own Lake manifest and build directory. It shares the parent's
pinned external package cache and imports the parent's standalone proof core.
It needs neither the old project nor its compiled artifacts to build. Comparing
against old absolute source paths is optional provenance checking only.

## What remains open

- An O(n^2) upper certificate for the larger one-bridge class is not established.
  Its nonemptiness and quadratic lower bound now both hold, but do not imply
  quadratic attainment. Its available explicit upper bound is exponential.
- The exact optimal exponential rate for the narrower class is not identified.
- Arbitrary nonseparable raw pointwise potentials, wider bridge interactions,
  other drift conditions, alternative initializations and repair rules are not
  excluded by the new obstruction.
- The linear process theorem and the certificate obstruction do not establish
  practical superiority, compiler-time complexity or adaptive-AI guarantees.
- Scientific priority remains unestablished. The primary-source comparison and
  proposed questions for a reviewer are in [LITERATURE.md](LITERATURE.md).
