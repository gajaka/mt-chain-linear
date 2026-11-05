"""Independent saved-evidence review of runtime-001; no root executor import."""

from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys


BASE = Path(__file__).resolve().parents[1]
RUN = BASE / "evidence/runtime-001"
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text())
plan = load(BASE / "PLAN.json")
result = load(RUN / "RESULT.json")
assert digest(BASE / "PLAN.json") == result["plan_sha256"]
assert digest(BASE / "provenance/run-v1.py") == result["executor_sha256"]
for item in plan["inputs"]:
    p = Path(item["path"])
    assert p.stat().st_size == item["bytes"] and digest(p) == item["sha256"], p

sys.path.insert(0, plan["source_root"])
import numpy as np
import pandas as pd
from cert_runner.certs.pp_graph import (
    _build_bin_distributions, _transport_operator, _local_plan_features, c_gen,
)

banks = load(RUN / "BANKS.json")
hazards = load(RUN / "HAZARDS.json")
pairs = load(RUN / "PAIRS.json")
contract = load(Path(plan["source_root"]) / "cert_runner/contracts/local_plan.json")
atoms = contract["certificates"]
assert len(atoms) == 4 and len(banks) == 8 and len(pairs) == 7
files = sorted(Path(plan["dataset_root"]).glob("*.csv"))
assert [p.name for p in files] == [b["name"] for b in banks]


def truth(snapshot, dataset):
    def atom(a):
        value = snapshot[a["field"]]
        assert not isinstance(value, bool)
        if isinstance(value, int):
            value = Fraction(value)
        else:
            assert math.isfinite(value)
            value = Fraction.from_float(value)
        bound = Fraction(*a["bound"])
        return {"gt": value > bound, "le": value <= bound, "eq": value == bound}[a["op"]]
    primitive = [atom(a) for a in atoms]
    return primitive + [all(primitive), primitive[1], snapshot["generator_cos"] > 0,
                        snapshot["dataset_key"] == dataset]


truths, invalidations, aggressive = [], [], []
max_error = 0.0
for b, (path, bank) in enumerate(zip(files, banks)):
    assert digest(path) == bank["source_sha256"]
    key = int(digest(path), 16)
    assert isinstance(bank["dataset_key"], int) and key == bank["dataset_key"]
    frame = pd.read_csv(path)
    assert len(frame) == bank["rows"]
    status, gen, _ = c_gen(frame)
    assert status == bank["gen_status"] and gen == bank["generator_cos"]
    bins = _build_bin_distributions(frame)
    assert bank["source_bins"] == [bins[0][0], bins[1][0]]
    source, target = bins[0][1], bins[1][1]
    _, optimal = _transport_operator(source, target)
    independent = np.outer(source, target)
    bt = []
    for j, candidate in enumerate(bank["candidates"]):
        assert j == candidate["index"] and candidate["fraction"] == j / 4
        matrix = (1 - j / 4) * independent + (j / 4) * optimal
        assert matrix.tolist() == candidate["matrix"]
        assert hashlib.sha256(matrix.tobytes()).hexdigest() == candidate["matrix_sha256"]
        assert np.isfinite(matrix).all() and np.min(matrix) >= 0
        error = max(float(np.max(np.abs(matrix.sum(axis=1) - source))),
                    float(np.max(np.abs(matrix.sum(axis=0) - target))))
        assert error < 1e-10 and error == candidate["marginal_error"]
        max_error = max(max_error, error)
        snapshot = dict(_local_plan_features(matrix), generator_cos=float(gen), dataset_key=key)
        assert snapshot == candidate["snapshot"]
        # Separate support/cycle calculation, independent of feature helper.
        support = [(i, k) for i in range(10) for k in range(10) if float(matrix[i, k]) > 1e-10]
        cycles = 0
        for n, (i, k) in enumerate(support):
            for u, v in support[n + 1:]:
                lhs = ((i-k)**2 + (u-v)**2) / 81
                rhs = ((i-v)**2 + (u-k)**2) / 81
                if lhs > rhs + 1e-10:
                    cycles += 1
        assert len(support) == snapshot["nnz"] and cycles == snapshot["violations"]
        row_masses = [math.fsum(float(x) for x in matrix[i]) for i in range(10)]
        fractions = [max(float(x) for x in matrix[i]) / row_masses[i]
                     for i in range(10) if row_masses[i] > 1e-10]
        assert len(fractions) == snapshot["valid_rows"]
        assert abs(statistics.fmean(fractions) - snapshot["monge_fraction"]) < 1e-14
        t = truth(snapshot, key)
        assert candidate["checks"] == t
        bt.append(t)
    truths.append(bt)
    expected_scopes, expected_witnesses = [], []
    for j in range(5):
        witnesses = {str(c): next(i for i in range(5) if bt[i][c] and not bt[j][c])
                     for c in range(8) if any(bt[i][c] and not bt[j][c] for i in range(5))}
        expected_witnesses.append(witnesses)
        expected_scopes.append([int(c) for c in witnesses])
    assert hazards[b] == dict(context=b, scopes=expected_scopes, witnesses=expected_witnesses)
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            bad = [c for c in range(8) if bt[i][c] and not bt[j][c]]
            if bad:
                invalidations.append(dict(context=b, before=i, after=j, invalidated=bad))
            if all(bt[i][c] or bt[j][c] for c in range(8)) != all(bt[j]):
                aggressive.append(dict(context=b, before=i, after=j))

expected = [dict(context=b, before=i, after=j, accepted=all(truths[b][j]))
            for b in range(8) for i in range(5) for j in range(5) if i != j]
skipped = sum(sum(truths[b][i][c] and c not in hazards[b]["scopes"][j] for c in range(8))
              for b in range(8) for i in range(5) for j in range(5) if i != j)
for n, pair in enumerate(pairs):
    assert [k for k in pair if k in ("B", "PPG")] == (["B", "PPG"] if n % 2 == 0 else ["PPG", "B"])
    for arm in ("B", "PPG"):
        assert pair[arm]["decisions"] == expected and pair[arm]["warm_decisions"] == expected
    assert pair["PPG"]["skipped_position_obligations"] == skipped
    assert not pair["errors"] and pair["PPG"]["wrong_skips"] == 0
for arm in load(RUN / "ABLATIONS.json").values():
    assert arm["decisions"] == expected and arm["wrong_skips"] == 0
assert load(RUN / "INVALIDATIONS.json") == invalidations and len(invalidations) == 56
assert load(RUN / "AGGRESSIVE_ERRORS.json") == aggressive and len(aggressive) == 28
for b, trace in enumerate(load(RUN / "TRACES.json")):
    current = 0
    expected_steps = []
    for j in [1, 2, 3, 4, 3, 2, 1, 0, 4]:
        accepted = all(truths[b][j])
        after = j if accepted else current
        expected_steps.append(dict(before=current, proposed=j, accepted=accepted, after=after))
        current = after
    assert trace == dict(context=b, steps=expected_steps, final=current)
controls = load(RUN / "CONTROLS.json")
assert len(controls) == 4 and all(c["rejected"] is True for c in controls)

old = load(Path(plan["source_root"]) / "cert_runner/contracts/boot320_plan_candidates.json")
boot320 = next(bank for bank in banks if bank["name"] == "boot320_merged_dawn.csv")
assert boot320["source_sha256"] == old["source_csv_sha256"]
for new, old_state in zip(boot320["candidates"], old["states"]):
    assert new["snapshot"] == old_state["snapshot"] and new["checks"] == old_state["checks"]
    assert new["matrix"] == old_state["coupling"]
negative_contexts = [bank["name"] for bank in banks if bank["generator_cos"] <= 0]
assert negative_contexts == ["boot334_dawn.csv"]
assert result["contexts_without_full_family_candidate"] == negative_contexts
assert sum(d["accepted"] for d in expected) == result["accepted_per_pass"] == 28
for arm in ("B", "PPG"):
    assert statistics.median(p[arm]["setup_seconds"] + p[arm]["cold_seconds"] for p in pairs) == result["cold_policy_medians"][arm]
    assert statistics.median(p[arm]["warm_seconds"] for p in pairs) == result["warm_policy_medians"][arm]
formal = load(BASE / "evidence/formal-001/RESULT.json")
assert formal["elapsed_seconds"] == result["measured_lean_setup_seconds"] == 8.506029334
assert formal["exit_code"] == 0
for item in plan["inputs"]:
    assert digest(Path(item["path"])) == item["sha256"]

report = dict(status="PASS_WITH_SCOPE_LIMITS", reviewed_utc=datetime.now(timezone.utc).isoformat(),
    scope="Independent finite runtime-001 audit; no root executor import or benchmark rerun",
    reviewed_executor=dict(path="provenance/run-v1.py", sha256=result["executor_sha256"]),
    checked=dict(contexts=8, numerical_candidate_matrices=40, exact_predicate_truth_values=320,
                 exact_scope_memberships=320, ordered_proposals=160, cold_warm_repetitions=7,
                 B_PPG_acceptance_decisions=160*7*4, accepted_per_pass=28,
                 genuine_invalidation_proposals=56, unsafe_aggressive_acceptances=28,
                 oracle_derived_trace_steps=72, primitive_guard_controls=4,
                 skipped_position_obligations_per_ppg_pass=skipped,
                 boot320_saved_bank_match=True, negative_GEN_retained=negative_contexts,
                 max_numerical_marginal_error=max_error),
    limitations=["Numerical producers/POT are reused as source computations, not formally verified",
        "Exact scopes cover only five declared snapshots in each context",
        "TRACES.json is oracle-derived, not executed B/PPG controller traces",
        "Controls exercise frame/rational primitives, not end-to-end proposal rejection",
        "Common preparation includes GEN/coupling/oracle preparation; do not add nested subtotals again",
        "Warm policy times exclude preparation; new Lean cost is PPG-specific and inherited setup is unknown",
        "Primitive comparisons are shared across duplicate/composite positions; position skips are not expensive computations saved",
        "No practical superiority, physical repair, universal Python refinement or novelty claim follows"],
    inputs=[dict(path=str(p.relative_to(BASE)), sha256=digest(p)) for p in
            [BASE/"PLAN.json", BASE/"provenance/run-v1.py", *sorted(RUN.glob('*.json'))]],
    reviewer_code_sha256=digest(Path(__file__)))
output = BASE / "evidence/RUNTIME_REVIEW-001.json"
with output.open("x") as stream:
    json.dump(report, stream, indent=2, allow_nan=False)
    stream.write("\n")
print(json.dumps(report["checked"], indent=2))
print("REVIEW PASS", output)
