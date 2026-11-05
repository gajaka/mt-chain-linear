"""Finite measured LUCES reuse comparison, explicitly without MT.

The new adapter calls unchanged numerical producers but retains negative GEN
contexts and external CSV paths. Imported research code is not formally verified.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import sys
from time import perf_counter


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    plan = json.loads((base / "PLAN.json").read_text())
    for item in plan["inputs"]:
        if sha(Path(item["path"])) != item["sha256"]:
            raise ValueError("Changed input: " + item["path"])
    args.output.mkdir(parents=True, exist_ok=False)
    started = datetime.now(timezone.utc).isoformat()
    preparation_start = perf_counter()
    sys.path.insert(0, plan["source_root"])
    import numpy as np
    import pandas as pd
    from cert_runner.certificate_contracts import snapshot_checks, rational, local_plan_contract_sha256
    from cert_runner.certs.pp_graph import _build_bin_distributions, _transport_operator, _local_plan_features, c_gen

    # Each output position remains distinct; memoization shares only identical
    # primitive predicates and their exact read values.
    def identity(snapshot):
        return tuple((name, rational(value)) for name, value in sorted(snapshot.items()))

    contexts, exported, gen_seconds, coupling_seconds = [], [], 0.0, 0.0
    for path in sorted(Path(plan["dataset_root"]).glob("*.csv")):
        frame = pd.read_csv(path)
        digest = sha(path)
        t = perf_counter()
        gen_status, gen_value, _ = c_gen(frame)
        gen_seconds += perf_counter() - t
        if gen_status == "N/A":
            raise ValueError("GEN unavailable; cannot silently encode it as false or zero")
        t = perf_counter()
        bins = _build_bin_distributions(frame)
        if len(bins) < 2:
            raise ValueError("Insufficient bins: " + path.name)
        source, target = bins[0][1], bins[1][1]
        _, optimal = _transport_operator(source, target)
        independent = np.outer(source, target)
        candidates = []
        for numerator in range(5):
            fraction = numerator / 4
            matrix = (1 - fraction) * independent + fraction * optimal
            error = max(float(np.max(np.abs(matrix.sum(axis=1) - source))),
                        float(np.max(np.abs(matrix.sum(axis=0) - target))))
            if error >= 1e-10:
                raise ValueError("Marginal check failed")
            candidates.append(dict(matrix=matrix, fingerprint=hashlib.sha256(matrix.tobytes()).hexdigest(),
                                   fraction=fraction, marginal_error=error))
        coupling_seconds += perf_counter() - t
        contexts.append(dict(name=path.name, digest=digest, dataset_key=int(digest, 16),
                             generator_cos=float(gen_value), gen_status=gen_status,
                             checks=snapshot_checks(int(digest, 16)), candidates=candidates,
                             bins=[bins[0][0], bins[1][0]], rows=len(frame)))

    class Engine:
        def __init__(self):
            self.features = {}
            self.atoms = {}
            self.stats = Counter()

        def state(self, ctx, index):
            candidate = ctx["candidates"][index]
            key = (ctx["digest"], candidate["fingerprint"])
            if key not in self.features:
                self.features[key] = _local_plan_features(candidate["matrix"])
                self.stats["feature_extractions"] += 1
            else:
                self.stats["feature_cache_hits"] += 1
            return dict(self.features[key], generator_cos=ctx["generator_cos"], dataset_key=ctx["dataset_key"])

        def check(self, predicate, state):
            if predicate.op == "all":
                return all(self.check(child, state) for child in predicate.args)
            self.stats["primitive_requests"] += 1
            # Producer and contract identities are fixed and hash-checked for
            # this entire run. Predicate identity includes its exact threshold.
            key = (predicate.op, predicate.field, predicate.bound, rational(state[predicate.field]))
            if key not in self.atoms:
                self.atoms[key] = predicate.evaluate(state)
                self.stats["primitive_evaluations"] += 1
            else:
                self.stats["primitive_cache_hits"] += 1
            return self.atoms[key]

        def all_positions(self, ctx, state):
            return [self.check(check, state) for check in ctx["checks"]]

    oracle_contexts = []
    oracle_start = perf_counter()
    for ctx in contexts:
        states = []
        truth = []
        for i, candidate in enumerate(ctx["candidates"]):
            state = dict(_local_plan_features(candidate["matrix"]), generator_cos=ctx["generator_cos"], dataset_key=ctx["dataset_key"])
            values = [check.evaluate(state) for check in ctx["checks"]]
            states.append(state)
            truth.append(values)
        oracle_contexts.append((states, truth))
        exported.append(dict(name=ctx["name"], source_sha256=ctx["digest"], source_bins=ctx["bins"],
            rows=ctx["rows"], gen_status=ctx["gen_status"], generator_cos=ctx["generator_cos"],
            dataset_key=ctx["dataset_key"], certificate_reads=[sorted(c.reads) for c in ctx["checks"]],
            candidates=[dict(index=i, fraction=c["fraction"], matrix=c["matrix"].tolist(),
                matrix_sha256=c["fingerprint"], marginal_error=c["marginal_error"],
                snapshot=states[i], checks=truth[i]) for i, c in enumerate(ctx["candidates"])]))
    oracle_preparation_seconds = perf_counter() - oracle_start
    common_preparation_seconds = perf_counter() - preparation_start

    def prepare_ppg(engine):
        tables = []
        for ctx in contexts:
            states = [engine.state(ctx, i) for i in range(5)]
            truth = [engine.all_positions(ctx, state) for state in states]
            scopes, witnesses = [], []
            for j in range(5):
                scope, witness = [], {}
                for c in range(8):
                    failing_before = [i for i in range(5) if truth[i][c] and not truth[j][c]]
                    if failing_before:
                        scope.append(c)
                        witness[str(c)] = failing_before[0]
                scopes.append(scope)
                witnesses.append(witness)
            tables.append(dict(states=states, truth=truth, scopes=scopes, witnesses=witnesses))
        return tables

    def frame(before, after):
        return (set(before) == set(after) and
                rational(before["generator_cos"]) == rational(after["generator_cos"]) and
                rational(before["dataset_key"]) == rational(after["dataset_key"]))

    def proposal(engine, b, i, j, tables=None, no_hazard=False, no_reuse=False):
        ctx = contexts[b]
        if no_reuse:
            engine.atoms.clear()
        before, after = engine.state(ctx, i), engine.state(ctx, j)
        if not frame(before, after):
            raise ValueError("Legitimate replacement broke protected frame")
        if tables is None or no_hazard:
            return all(engine.check(c, after) for c in ctx["checks"]), set()
        table = tables[b]
        # Re-establish explicit same-context source/target bank membership.
        if identity(before) != identity(table["states"][i]) or identity(after) != identity(table["states"][j]):
            raise ValueError("State outside declared same-context bank")
        prior = table["truth"][i]
        required = {c for c in range(8) if not prior[c] or c in table["scopes"][j]}
        omitted = set(range(8)) - required
        accepted = all(engine.check(ctx["checks"][c], after) for c in sorted(required))
        return accepted, omitted

    def run_workload(engine, tables=None, no_hazard=False, no_reuse=False):
        decisions, skipped, wrong_skips = [], 0, 0
        for b, ctx in enumerate(contexts):
            states_ref, truth_ref = oracle_contexts[b]
            for i in range(5):
                for j in range(5):
                    if i == j:
                        continue
                    accepted, omitted = proposal(engine, b, i, j, tables, no_hazard, no_reuse)
                    skipped += len(omitted)
                    wrong_skips += sum(not truth_ref[j][c] for c in omitted)
                    decisions.append(dict(context=b, before=i, after=j, accepted=accepted))
        return dict(decisions=decisions, skipped_position_obligations=skipped, wrong_skips=wrong_skips)

    repetitions = []
    first_tables = None
    for repetition in range(7):
        pair = {}
        order = ["B", "PPG"] if repetition % 2 == 0 else ["PPG", "B"]
        for name in order:
            engine = Engine()
            start = perf_counter()
            tables = prepare_ppg(engine) if name == "PPG" else None
            setup_seconds = perf_counter() - start
            start = perf_counter()
            cold = run_workload(engine, tables)
            cold_seconds = perf_counter() - start
            cold_stats = dict(engine.stats)
            start = perf_counter()
            warm = run_workload(engine, tables)
            warm_seconds = perf_counter() - start
            pair[name] = dict(setup_seconds=setup_seconds, cold_seconds=cold_seconds,
                warm_seconds=warm_seconds, cold_stats=cold_stats, final_stats=dict(engine.stats),
                decisions=cold["decisions"], warm_decisions=warm["decisions"],
                skipped_position_obligations=cold["skipped_position_obligations"], wrong_skips=cold["wrong_skips"])
            if first_tables is None and name == "PPG":
                first_tables = tables
        validation_start = perf_counter()
        errors = []
        # A fresh uncached feature extraction and full original checker call
        # validates every proposal independently of both policy caches.
        for n, decision in enumerate(pair["B"]["decisions"]):
            b, j = decision["context"], decision["after"]
            ctx = contexts[b]
            state = dict(_local_plan_features(ctx["candidates"][j]["matrix"]),
                         generator_cos=ctx["generator_cos"], dataset_key=ctx["dataset_key"])
            expected = all(check.evaluate(state) for check in ctx["checks"])
            for name in ("B", "PPG"):
                for key in ("decisions", "warm_decisions"):
                    if pair[name][key][n]["accepted"] != expected:
                        errors.append(dict(arm=name, key=key, decision=n))
        pair["independent_validation_seconds"] = perf_counter() - validation_start
        pair["errors"] = errors
        repetitions.append(pair)
    if any(p["errors"] or p["PPG"]["wrong_skips"] for p in repetitions):
        raise ValueError("Unsafe policy result")

    ablations = {}
    for name, kwargs in (("NO_HAZARD", dict(no_hazard=True)), ("NO_OBSERVABLE_REUSE", dict(no_hazard=True, no_reuse=True))):
        engine = Engine()
        start = perf_counter()
        tables = prepare_ppg(engine)
        outcome = run_workload(engine, tables, **kwargs)
        ablations[name] = dict(seconds=perf_counter() - start, stats=dict(engine.stats), **outcome)
        if outcome["decisions"] != repetitions[0]["B"]["decisions"]:
            raise ValueError("Ablation disagreement")
    aggressive_errors = []
    actual_invalidations = []
    for b, (states, truth) in enumerate(oracle_contexts):
        for i in range(5):
            for j in range(5):
                if i == j:
                    continue
                bad = [c for c in range(8) if truth[i][c] and not truth[j][c]]
                if bad:
                    actual_invalidations.append(dict(context=b, before=i, after=j, invalidated=bad))
                # Negative control retains prior PASS and checks only prior failures.
                naive = all(truth[i][c] or truth[j][c] for c in range(8))
                if naive != all(truth[j]):
                    aggressive_errors.append(dict(context=b, before=i, after=j))

    traces = {}
    for name in ["B", "PPG"]:
        engine = Engine()
        tables = prepare_ppg(engine) if name == "PPG" else None
        arm_traces = []
        for b, ctx in enumerate(contexts):
            current, steps = 0, []
            for proposed in [1, 2, 3, 4, 3, 2, 1, 0, 4]:
                accepted, omitted = proposal(engine, b, current, proposed, tables)
                expected = all(oracle_contexts[b][1][proposed])
                if accepted != expected or any(not oracle_contexts[b][1][proposed][c] for c in omitted):
                    raise ValueError("Unsafe sequential trace result")
                steps.append(dict(before=current, proposed=proposed, accepted=accepted,
                                  after=proposed if accepted else current,
                                  skipped_positions=sorted(omitted)))
                if accepted:
                    current = proposed
            arm_traces.append(dict(context=b, steps=steps, final=current))
        traces[name] = dict(contexts=arm_traces, stats=dict(engine.stats))

    # Boundary controls are outside the proved replacement operation. The same
    # standard frame/input validation rejects them for either controller.
    before = oracle_contexts[0][0][4]
    controls = []
    for field, value in [("generator_cos", -1.0), ("dataset_key", contexts[0]["dataset_key"] + 1)]:
        after = dict(before, **{field: value})
        controls.append(dict(name="protected_change_" + field, rejected=not frame(before, after)))
    for value in [True, float("nan")]:
        try:
            rational(value)
            rejected = False
        except (TypeError, ValueError):
            rejected = True
        controls.append(dict(name="invalid_numeric_" + repr(value), rejected=rejected))
    if not all(c["rejected"] for c in controls):
        raise ValueError("Negative input control accepted")

    dump(args.output / "BANKS.json", exported)
    dump(args.output / "HAZARDS.json", [dict(context=b, scopes=t["scopes"], witnesses=t["witnesses"]) for b, t in enumerate(first_tables)])
    dump(args.output / "PAIRS.json", repetitions)
    dump(args.output / "ABLATIONS.json", ablations)
    dump(args.output / "INVALIDATIONS.json", actual_invalidations)
    dump(args.output / "AGGRESSIVE_ERRORS.json", aggressive_errors)
    dump(args.output / "TRACES.json", traces)
    dump(args.output / "CONTROLS.json", controls)
    for item in plan["inputs"]:
        if sha(Path(item["path"])) != item["sha256"]:
            raise ValueError("Input changed during run")
    result = dict(status="COMPLETE_FINITE_STUDY; NO_MT", started_utc=started,
        finished_utc=datetime.now(timezone.utc).isoformat(), plan_sha256=sha(base / "PLAN.json"),
        executor_sha256=sha(Path(__file__)), versions={n: importlib.metadata.version(n) for n in ("numpy", "pandas", "scipy", "POT")},
        contexts=len(contexts), candidates=sum(len(c["candidates"]) for c in contexts),
        proposals_per_pass=len(repetitions[0]["B"]["decisions"]),
        accepted_per_pass=sum(d["accepted"] for d in repetitions[0]["B"]["decisions"]),
        contexts_without_full_family_candidate=[c["name"] for b, c in enumerate(contexts) if not any(all(t) for t in oracle_contexts[b][1])],
        common_preparation_seconds=common_preparation_seconds, gen_preparation_seconds=gen_seconds,
        coupling_preparation_seconds=coupling_seconds, oracle_preparation_seconds=oracle_preparation_seconds,
        measured_lean_setup_seconds=8.506029334, inherited_framework_setup="Historical/unmeasured, not zero",
        wrong_acceptances=0, wrong_ppg_skips=0,
        unsafe_aggressive_acceptances=len(aggressive_errors), proposals_with_invalidation=len(actual_invalidations),
        same_strong_baseline_decisions=True,
        cold_policy_medians={name: float(np.median([p[name]["setup_seconds"] + p[name]["cold_seconds"] for p in repetitions])) for name in ("B", "PPG")},
        warm_policy_medians={name: float(np.median([p[name]["warm_seconds"] for p in repetitions])) for name in ("B", "PPG")},
        independent_validation_median=float(np.median([p["independent_validation_seconds"] for p in repetitions])),
        ppg_new_setup_and_cold_faster_pairs=sum(p["PPG"]["setup_seconds"] + p["PPG"]["cold_seconds"] + 8.506029334 < p["B"]["setup_seconds"] + p["B"]["cold_seconds"] for p in repetitions),
        scoped_preservation_demonstrated=True, practical_superiority_demonstrated=False,
        scope="Constructed finite coupling-replacement workload on measured marginals; not physical controller repairs, raw-coupling quotient closure, Python refinement or novelty")
    dump(args.output / "RESULT.json", result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
