# Measured finite certificate instance

These files bind the Lean instance to one boot320 transport problem from the
companion `master-controler` runner.

- `local_plan.json` is the runner's normative comparison contract. The strict
  Monge threshold is the exact rational value of Python's binary64 `0.69`.
- `local_plan_kernel_inputs.json` contains five six-field snapshots as exact
  numerator/denominator pairs, with CSV and contract hashes. The candidates mix
  an independent coupling with the numerical POT optimum in quarters.
- `local_plan_kernel_inputs.txt` is a readable rendering of those same ratios.

From the Lean repository, with the runner in the adjacent directory:

```sh
python3 tools/export_luces_instance.py --runner-root ../master-controler --check
lake build PPGraph.Integration.LucesCertificateRepair
python3 tools/audit_ppgraph.py
```

Omit `--check` to regenerate the data module and these input files after a
deliberate runner update. The exporter checks CSV, contract and producer hashes;
the runner's `cert_runner.local_plan_binding --check` also recomputes the matrices
and extracted features. Lean's pure reader decodes these particular JSON files,
and the kernel proves the resulting finite search, restoration and preservation.
The audit freshly elaborates the input owners even with a warm Lake cache.

The coupling solver and feature extraction are numerically checked provenance,
not formal proofs of Python, NumPy, POT or physical controller execution. See
[the theorem scope](../../docs/THEOREM_SCOPE.md#finite-read-measured-instance).
