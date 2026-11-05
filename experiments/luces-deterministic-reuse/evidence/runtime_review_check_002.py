"""Independent stdlib evidence/delta review; no benchmark or executor import."""

from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import statistics


BASE = Path(__file__).resolve().parents[1]
RUN = BASE / "evidence/runtime-002"
OLD = BASE / "evidence/runtime-001"
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text())
plan = load(BASE / "PLAN.json")
result = load(RUN / "RESULT.json")
prior = load(BASE / "evidence/RUNTIME_REVIEW-001.json")
assert prior["status"] == "PASS_WITH_SCOPE_LIMITS"
for item in prior["inputs"]:
    assert digest(BASE / item["path"]) == item["sha256"], item
assert digest(BASE / "evidence/runtime_review_check_001.py") == prior["reviewer_code_sha256"]
assert digest(BASE / "run.py") == result["executor_sha256"] == "602df7136067bb7fccd6bbb2412d705a869b8964f985d0b9b35e9466a0fbe832"
assert digest(BASE / "PLAN.json") == result["plan_sha256"]
for item in plan["inputs"]:
    path = Path(item["path"])
    assert path.stat().st_size == item["bytes"] and digest(path) == item["sha256"], path

unchanged = ["BANKS.json", "HAZARDS.json", "INVALIDATIONS.json", "AGGRESSIVE_ERRORS.json", "CONTROLS.json"]
for name in unchanged:
    assert digest(OLD / name) == digest(RUN / name), name
banks = load(RUN / "BANKS.json")
hazards = load(RUN / "HAZARDS.json")
contract = load(Path(plan["source_root"]) / "cert_runner/contracts/local_plan.json")
atoms = contract["certificates"]


def rational(value):
    assert not isinstance(value, bool)
    if isinstance(value, int):
        return Fraction(value)
    assert isinstance(value, float) and math.isfinite(value)
    return Fraction.from_float(value)


def descriptor(bank, position):
    if position < 4:
        a = atoms[position]
        return a["op"], a["field"], Fraction(*a["bound"])
    if position == 5:
        return descriptor(bank, 1)
    if position == 6:
        return "gt", "generator_cos", Fraction(0)
    if position == 7:
        return "eq", "dataset_key", Fraction(bank["dataset_key"])
    raise ValueError(position)


def predicate(bank, state, position):
    if position == 4:
        return all(predicate(bank, state, c) for c in range(4))
    op, field, bound = descriptor(bank, position)
    value = rational(state[field])
    return {"gt": value > bound, "le": value <= bound, "eq": value == bound}[op]


truths = []
for b, bank in enumerate(banks):
    path = Path(plan["dataset_root"]) / bank["name"]
    assert digest(path) == bank["source_sha256"]
    assert int(digest(path), 16) == bank["dataset_key"]
    bt = []
    for state in bank["candidates"]:
        assert state["snapshot"]["generator_cos"] == bank["generator_cos"]
        assert state["snapshot"]["dataset_key"] == bank["dataset_key"]
        truth = [predicate(bank, state["snapshot"], c) for c in range(8)]
        assert truth == state["checks"]
        bt.append(truth)
    truths.append(bt)
    for j in range(5):
        scope = [c for c in range(8) if any(bt[i][c] and not bt[j][c] for i in range(5))]
        witnesses = {str(c): next(i for i in range(5) if bt[i][c] and not bt[j][c]) for c in scope}
        assert hazards[b]["scopes"][j] == scope and hazards[b]["witnesses"][j] == witnesses


class AuditEngine:
    """Reconstruct counters from exact saved states without numerical producers."""

    def __init__(self, ppg=False):
        self.stats = Counter()
        self.feature_keys = set()
        self.atom_values = {}
        if ppg:
            for b in range(8):
                for i in range(5):
                    state = self.state(b, i)
                    for c in range(8):
                        assert self.check(b, state, c) == truths[b][i][c]

    def state(self, b, i):
        bank = banks[b]
        candidate = bank["candidates"][i]
        key = bank["source_sha256"], candidate["matrix_sha256"]
        if key in self.feature_keys:
            self.stats["feature_cache_hits"] += 1
        else:
            self.feature_keys.add(key)
            self.stats["feature_extractions"] += 1
        return candidate["snapshot"]

    def check(self, b, state, c):
        if c == 4:
            return all(self.check(b, state, k) for k in range(4))
        self.stats["primitive_requests"] += 1
        op, field, bound = descriptor(banks[b], c)
        key = op, field, bound, rational(state[field])
        if key in self.atom_values:
            self.stats["primitive_cache_hits"] += 1
        else:
            self.stats["primitive_evaluations"] += 1
            self.atom_values[key] = predicate(banks[b], state, c)
        return self.atom_values[key]

    def step(self, b, i, j, ppg=False, clear=False):
        if clear:
            self.atom_values.clear()
        before, after = self.state(b, i), self.state(b, j)
        assert set(before) == set(after)
        assert before["generator_cos"] == after["generator_cos"]
        assert before["dataset_key"] == after["dataset_key"]
        required = [c for c in range(8) if not ppg or not truths[b][i][c] or c in hazards[b]["scopes"][j]]
        omitted = [c for c in range(8) if c not in required]
        accepted = all(self.check(b, after, c) for c in required)
        assert all(truths[b][j][c] for c in omitted)
        assert accepted == all(truths[b][j])
        return accepted, omitted


def workload(engine, ppg=False, clear=False):
    decisions, skipped = [], 0
    for b in range(8):
        for i in range(5):
            for j in range(5):
                if i != j:
                    accepted, omitted = engine.step(b, i, j, ppg, clear)
                    decisions.append(dict(context=b, before=i, after=j, accepted=accepted))
                    skipped += len(omitted)
    return decisions, skipped


pairs = load(RUN / "PAIRS.json")
old_pairs = load(OLD / "PAIRS.json")
assert len(pairs) == 7
for repetition, pair in enumerate(pairs):
    assert [k for k in pair if k in ("B", "PPG")] == (["B", "PPG"] if repetition % 2 == 0 else ["PPG", "B"])
    assert not pair["errors"]
    for arm in ("B", "PPG"):
        engine = AuditEngine(ppg=arm == "PPG")
        decisions, skipped = workload(engine, ppg=arm == "PPG")
        assert decisions == pair[arm]["decisions"] == old_pairs[repetition][arm]["decisions"]
        assert dict(engine.stats) == pair[arm]["cold_stats"]
        decisions_warm, skipped_warm = workload(engine, ppg=arm == "PPG")
        assert decisions_warm == decisions == pair[arm]["warm_decisions"]
        assert dict(engine.stats) == pair[arm]["final_stats"]
        assert skipped == skipped_warm == pair[arm]["skipped_position_obligations"]
        assert pair[arm]["wrong_skips"] == 0
        assert sum(d["accepted"] for d in decisions) == 28
    assert pair["PPG"]["skipped_position_obligations"] == 492
for name, arm in load(RUN / "ABLATIONS.json").items():
    engine = AuditEngine(ppg=True)
    expected, skipped = workload(engine, clear=name == "NO_OBSERVABLE_REUSE")
    assert arm["decisions"] == expected and arm["stats"] == dict(engine.stats)
    assert skipped == arm["skipped_position_obligations"] == 0 and arm["wrong_skips"] == 0

traces = load(RUN / "TRACES.json")
trace_counts = {}
for arm in ("B", "PPG"):
    engine = AuditEngine(ppg=arm == "PPG")
    contexts, committed, rolled_back, omitted_count = [], 0, 0, 0
    for b in range(8):
        current, steps = 0, []
        for proposed in [1, 2, 3, 4, 3, 2, 1, 0, 4]:
            accepted, omitted = engine.step(b, current, proposed, ppg=arm == "PPG")
            after = proposed if accepted else current
            steps.append(dict(before=current, proposed=proposed, accepted=accepted,
                              after=after, skipped_positions=omitted))
            current = after
            committed += int(accepted)
            rolled_back += int(not accepted)
            omitted_count += len(omitted)
        contexts.append(dict(context=b, steps=steps, final=current))
    assert traces[arm] == dict(contexts=contexts, stats=dict(engine.stats))
    trace_counts[arm] = dict(steps=72, accepted_steps=committed, rejected_rolled_back_steps=rolled_back,
                             omitted_position_obligations=omitted_count, stats=dict(engine.stats))

for arm in ("B", "PPG"):
    assert statistics.median(p[arm]["setup_seconds"] + p[arm]["cold_seconds"] for p in pairs) == result["cold_policy_medians"][arm]
    assert statistics.median(p[arm]["warm_seconds"] for p in pairs) == result["warm_policy_medians"][arm]
assert statistics.median(p["independent_validation_seconds"] for p in pairs) == result["independent_validation_median"]
assert result["ppg_new_setup_and_cold_faster_pairs"] == sum(p["PPG"]["setup_seconds"] + p["PPG"]["cold_seconds"] + result["measured_lean_setup_seconds"] < p["B"]["setup_seconds"] + p["B"]["cold_seconds"] for p in pairs) == 0
assert result["measured_lean_setup_seconds"] == load(BASE / "evidence/formal-001/RESULT.json")["elapsed_seconds"] == 8.506029334
assert result["wrong_acceptances"] == result["wrong_ppg_skips"] == 0
assert result["proposals_with_invalidation"] == len(load(RUN / "INVALIDATIONS.json")) == 56
assert result["unsafe_aggressive_acceptances"] == len(load(RUN / "AGGRESSIVE_ERRORS.json")) == 28
assert result["practical_superiority_demonstrated"] is False

supplement = load(BASE / "evidence/PROTECTED_REUSE.json")
assert supplement["executor_sha256"] == digest(BASE / "protected_reuse.py")
assert supplement["plan_sha256"] == digest(BASE / "PROTECTED_REUSE_PLAN.json")
assert supplement["banks_sha256"] == digest(RUN / "BANKS.json")
supplement_decisions = [all(truths[b][j]) for b in range(8) for i in range(5) for j in range(5) if i != j]
for arm, calls in (("FIXED_VIEW_REUSE", 8), ("RECOMPUTE_PROTECTED", 160)):
    record = supplement["arms"][arm]
    assert record["protected_producer_calls"] == calls
    assert record["proposals"] == len(record["decisions"]) == len(supplement_decisions) == 160
    assert record["decisions"] == supplement_decisions and record["accepted"] == 28
    assert record["seconds"] > 0
assert supplement["source_hashes_unchanged"] is True
for item in plan["inputs"]:
    assert digest(Path(item["path"])) == item["sha256"]

report = dict(status="PASS_WITH_SCOPE_LIMITS", reviewed_utc=datetime.now(timezone.utc).isoformat(),
    scope="Independent stdlib runtime-002 delta and protected-producer supplement review; no executor import or timing rerun",
    reviewed_executor=dict(path="run.py", sha256=result["executor_sha256"]),
    previous_review=dict(path="evidence/RUNTIME_REVIEW-001.json", sha256=digest(BASE / "evidence/RUNTIME_REVIEW-001.json"),
        inherited="Fresh numerical producer rebuild of all 40 matrices/snapshots, separate support/cycle calculation, source pins, boot320 original saved-bank match, negative GEN retained"),
    checked=dict(unchanged_artifacts_from_fresh_verified_001=unchanged,
        exact_predicate_truth_values=320, exact_scope_memberships_and_witnesses=320,
        B_PPG_cold_warm_acceptance_decisions=4480, accepted_per_pass=28,
        skipped_position_obligations_per_ppg_pass=492, wrong_skips=0,
        invalidating_proposals=56, aggressive_false_acceptances=28,
        all_recorded_workload_and_trace_cache_counters_match_independent_emulation=True,
        actual_controller_trace_counts=trace_counts,
        protected_supplement=dict(reuse_producer_calls=8, recompute_producer_calls=160,
            proposals_per_arm=160, accepted_per_arm=28, exact_recorded_decisions_match=True,
            producer_recomputation_not_rerun_in_delta_review=True)),
    limitations=[
        "Numerical producer/POT correctness and source-code correspondence are not kernel-proved; unchanged source-producer checks are inherited by exact artifact hashes from runtime001 review",
        "Semantic scopes and source/target membership cover only five declared snapshots per fixed CSV context",
        "Sequential traces now execute the same proposal helper as measured arms; they are constructed finite coverage workloads, not physical repair episodes",
        "Four negative controls test frame/rational primitives only, not end-to-end malformed proposal handling",
        "B shares exact primitive predicate identities/values and feature fingerprints; duplicate and composite checks share atoms; 492 omitted positions are not 492 expensive computations saved",
        "NO_OBSERVABLE_REUSE combines no-hazard selection with atom-cache clearing; protected supplement isolates only producer-level unchanged GEN/dataset reuse",
        "Protected supplement uses unchanged preloaded frames and context-index cache keys within a hash-checked fixed context lifetime; it is not a general file-change invalidation implementation",
        "Protected supplement timing is one ordered pair, excludes frame loading and shared source checks, and ordinary dependency caching obtains the same 8-versus-160 reuse",
        "Common preparation includes nested GEN/coupling/oracle preparation; do not add these subtotals again",
        "Warm timings exclude preparation; 8.506029334 seconds measured Lean setup is additional PPG cost, while inherited setup cost is unknown",
        "No practical superiority, physical controller repair, MT guarantee, universal Python refinement or scientific novelty follows"],
    bindings=[dict(path=str(p.relative_to(BASE)), sha256=digest(p)) for p in
        [BASE/"PLAN.json", BASE/"run.py", BASE/"PROTECTED_REUSE_PLAN.json", BASE/"protected_reuse.py",
         BASE/"evidence/PROTECTED_REUSE.json", *sorted(RUN.glob("*.json"))]],
    reviewer_code_sha256=digest(Path(__file__)))
output = BASE / "evidence/RUNTIME_REVIEW-002.json"
with output.open("x") as stream:
    json.dump(report, stream, indent=2, allow_nan=False)
    stream.write("\n")
print(json.dumps(report["checked"], indent=2))
print("REVIEW PASS", output)
