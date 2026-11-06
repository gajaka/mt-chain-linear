# Source identity checks

`module-migration/before/` contains the original versions of the chain sources,
build configuration and audit tools before their Lean module-header migration.
These files are inputs to `scripts/provenance.py`, not another implementation
or an additional mathematical premise.

The checker compares them with [SOURCE_MANIFEST.json](../SOURCE_MANIFEST.json),
replays the permitted transformations recorded in
[MODULE_MIGRATION.json](../MODULE_MIGRATION.json), and verifies the current
sources byte for byte. The certificate-study source check uses the same
validation. Removing these inputs would break the advertised checks.

Only source-verification inputs are retained here. Local workspace cleanup
records and publication preparation are not part of this directory.
