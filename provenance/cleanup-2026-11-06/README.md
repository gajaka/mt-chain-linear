# Focused branch cleanup, 2026-11-06

## Pre-commit review follow-up

Before the cleanup commit, the user identified window-locality as a
mathematical continuation worth retaining. Its 60 tracked files were restored
byte-for-byte from the archive and checked against HEAD and their manifest.
All seven finite optimum certificates and the local 91-row/432-column
identity were rechecked exactly. The width-two all-n obstruction remains
paper-only. `make check` now includes these stored-certificate checks.

The original cleanup `RESULT.json` and path index below describe the initial
403-file archival action. They are preserved as history, not rewritten as a
claim about the final tree: 60 files were restored, leaving 343 tracked paths
archived outside the repository. `FINALIZATION.json` records the final scope,
checks, and separate local documentation commits preserving the C5 finding
in LUCES and cert_runner. No C5 implementation or historical output changed.

## Initial cleanup record

The user requested cleaning the whole branch before preparing external review.
The active project now contains the original uniform MT proof, certificate
existence/separation, biased resampling, and the Crew/barrier negative findings.

Unrelated trees were moved outside the repository, preserving all bytes:

- vendor/ and framework/: original generic PPG library and separate build.
- evidence/framework/: their verification evidence.
- experiments/luces-log-replay/ and experiments/luces-deterministic-reuse/.
- research/window-locality/: a separate valid study, outside this review scope.
- review/: unfinished contact drafts, packet and bundler prepared before the
  user changed the priority to branch cleanup.

Archive: /Users/gajaka/projects/mt-chain-linear-archive/cleanup-20261106T121933Z

No source repository outside this project was changed. Archival is a scope
change, not a mathematical rejection of the archived studies.

The archive contains BEFORE.json, OLD_PATH_RESOLUTION.json, original copies
of README.md/AGENTS.md/Makefile, and all removed trees. Every archived file was
checked against its pre-move hash. ARCHIVED_PATHS.json in this directory
indexes the removed tracked paths, original documents and new review sources.
The full archive index also covers ignored local build artifacts. Symbolic
link targets are preserved verbatim; restore original paths before attempting
to run an archived workspace. It is historical evidence, not a relocated build.

Root README, AGENTS and Makefile were updated for the focused project.
Mathematical source bodies, build dependency pins, source manifests and
historical proof receipts were not edited. Required extraction provenance
and root audit history remain in place because validators and current
receipts reference them.

Crew's historical FORMAL_INPUTS.json binds the former root AGENTS.md and
nine files from the archived framework. Those exact bytes resolve through
ARCHIVED_PATHS.json. The old Crew protocol and receipt remain unchanged;
their old relative framework links now refer to archived context. The
original input files can be recovered without changing that historical record.

make check passed after cleanup: strict Lean builds of the core and both
research studies, both source validators, and the independent rational
barrier checker. Existing dependency/build caches were reused. There is no
new second-kernel or human scientific review implied by this check.

RESULT.json and make-check.log record the cleanup verification. The archive
is local and outside Git; it is not silently included in a source checkout.
No message was sent and no remote push was performed during this cleanup.
