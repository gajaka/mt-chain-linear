#!/usr/bin/env python3
"""Compute finite-chain means and retain exact rational Bellman certificates.

Requires python-flint. The generator uses the exact strong/weak label quotient;
verify.py independently reconstructs original draws when checking its output.
The preselected barrier policy and n <= 5 scope are fixed by PROTOCOL.md.
"""

from __future__ import annotations

import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
import itertools
import json
from pathlib import Path
import platform
import sys
import time

import flint
from flint import fmpq, fmpq_mat


HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
PROTOCOL_SHA256 = "317b4f51af8ffe8399bcc12433ef8a916d7e884f981509353ac42ae23cc9603b"
STATE_ORDER = "thresholds_lex_then_labels_lex;0=strong;1=weak"
SOURCE_PATHS = (
    "experiments/barrier-guided-bias/PROTOCOL.md",
    "experiments/barrier-guided-bias/run.py",
    "experiments/barrier-guided-bias/verify.py",
    "formal/mt/core/Chain.lean",
    "formal/mt/core/FreshDraws.lean",
    "formal/mt/core/Features.lean",
    "formal/mt/core/ChainKernel.lean",
    "research/biased-resampling/formal/BiasedDefinitions.lean",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    """Create one new evidence file; never replace an existing receipt."""
    with path.open("x", encoding="ascii") as stream:
        json.dump(value, stream, indent=2, ensure_ascii=True)
        stream.write("\n")


def build_model(n: int) -> dict:
    """Enumerate quotient states and unweighted possible local redraws.

    A quotient label 0 has multiplicity three among the original four labels.
    Endpoint draws are marginalized, so only mutable thresholds are enumerated.
    Each transition record is (successor index, new threshold values, new label).
    """
    states = [
        (values, labels)
        for values in itertools.product(range(3), repeat=n - 1)
        for labels in itertools.product(range(2), repeat=n)
    ]
    index = {state: k for k, state in enumerate(states)}
    transitions = []
    failure = []
    barrier = []
    for values, labels in states:
        thresholds = (2,) + values + (0,)
        bad = [
            i
            for i in range(n)
            if not (
                thresholds[i] == thresholds[i + 1]
                if labels[i] == 1
                else thresholds[i + 1] <= thresholds[i]
            )
        ]
        if not bad:
            failure.append(None)
            barrier.append(n)
            transitions.append(None)
            continue
        i = bad[0]
        height = max(
            (
                j + 1
                for j in range(i)
                if thresholds[j] == 2 and labels[j] == 0
            ),
            default=0,
        )
        assert 0 <= height <= i
        failure.append(i)
        barrier.append(height)
        mutable = [j for j in (i, i + 1) if 1 <= j < n]
        row = []
        for new_values in itertools.product(range(3), repeat=len(mutable)):
            updated_values = list(values)
            for j, value in zip(mutable, new_values):
                updated_values[j - 1] = value
            for new_label in range(2):
                updated_labels = list(labels)
                updated_labels[i] = new_label
                successor = index[(tuple(updated_values), tuple(updated_labels))]
                row.append((successor, new_values, new_label))
        transitions.append(row)
    weights = [
        fmpq(3 ** labels.count(0), 3 ** (n - 1) * 4**n)
        for _, labels in states
    ]
    assert sum(weights, fmpq(0)) == 1
    return {
        "n": n,
        "states": states,
        "transitions": transitions,
        "failure": failure,
        "barrier": barrier,
        "initial_weights": weights,
    }


def weighted_rows(model: dict, policy: str, p: fmpq | None) -> list:
    """Aggregate exact transition masses, deleting zero-probability edges."""
    rows = []
    for k, transitions in enumerate(model["transitions"]):
        if transitions is None:
            rows.append(None)
            continue
        bias = p if policy == "static" else fmpq(
            int(model["failure"][k] == model["barrier"][k])
        )
        assert bias is not None and 0 <= bias <= 1
        thresholds = [(1 - bias) / 2, (1 - bias) / 2, bias]
        row = {}
        for successor, new_values, new_label in transitions:
            mass = fmpq(1 if new_label else 3, 4)
            for value in new_values:
                mass *= thresholds[value]
            if mass:
                row[successor] = row.get(successor, fmpq(0)) + mass
        assert sum(row.values(), fmpq(0)) == 1
        rows.append(row)
    return rows


def strongly_connected(rows: list) -> list[list[int]]:
    """Tarjan components, returned with successor components first."""
    count = len(rows)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 4 * count + 100))
    indices = [-1] * count
    lowlink = [-1] * count
    stack = []
    on_stack = set()
    components = []
    next_index = 0

    def visit(v: int) -> None:
        nonlocal next_index
        indices[v] = lowlink[v] = next_index
        next_index += 1
        stack.append(v)
        on_stack.add(v)
        for w in rows[v] or ():
            if indices[w] < 0:
                visit(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            component = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                component.append(w)
                if w == v:
                    break
            components.append(component)

    for v in range(count):
        if indices[v] < 0:
            visit(v)
    return components


def absorption_check(rows: list, components: list[list[int]]) -> tuple[list, int]:
    """Find closed active components and count states with a path to Good.

    Every original uniform-start state has positive probability. Thus even one
    closed active component forces infinite initialized expected stopping time.
    """
    closed_active = []
    for component in components:
        if rows[component[0]] is None:
            continue
        members = set(component)
        if all(j in members for k in component for j in rows[k]):
            closed_active.append(sorted(component))
    predecessors = [[] for _ in rows]
    reachable = {k for k, row in enumerate(rows) if row is None}
    pending = deque(reachable)
    for k, row in enumerate(rows):
        for j in row or ():
            predecessors[j].append(k)
    while pending:
        for parent in predecessors[pending.popleft()]:
            if parent not in reachable:
                reachable.add(parent)
                pending.append(parent)
    return closed_active, len(reachable)


def solve(model: dict, policy: str, p: fmpq | None) -> tuple[dict, dict]:
    """Solve exact rational Bellman equations component by component."""
    started = time.perf_counter()
    rows = weighted_rows(model, policy, p)
    components = strongly_connected(rows)
    closed, reachable = absorption_check(rows, components)
    metadata = {
        "n": model["n"],
        "policy": policy,
        "p": str(p) if p is not None else None,
        "state_count": len(rows),
        "active_state_count": sum(row is not None for row in rows),
        "scc_count": len(components),
        "largest_scc": max(map(len, components)),
        "states_with_path_to_good": reachable,
        "closed_active_scc_count": len(closed),
    }
    certificate = {
        "schema_version": 1,
        "n": model["n"],
        "policy": policy,
        "p": metadata["p"],
        "state_order": STATE_ORDER,
    }
    if closed:
        metadata.update(expected="infinite", expected_decimal=None)
        certificate["closed_active_components"] = closed
    else:
        assert reachable == len(rows)
        h = [fmpq(0)] * len(rows)
        done = set()
        for component in components:
            if rows[component[0]] is None:
                done.update(component)
                continue
            local = {k: i for i, k in enumerate(component)}
            matrix = fmpq_mat(len(component), len(component))
            rhs = fmpq_mat(len(component), 1)
            for k, i in local.items():
                matrix[i, i] = 1
                rhs[i, 0] = 1
                for j, mass in rows[k].items():
                    if j in local:
                        matrix[i, local[j]] -= mass
                    else:
                        assert j in done
                        rhs[i, 0] += mass * h[j]
            answer = matrix.solve(rhs, algorithm="dixon" if len(component) > 30 else None)
            for k, i in local.items():
                h[k] = answer[i, 0]
            done.update(component)
        assert all(value >= 0 for value in h)
        for k, row in enumerate(rows):
            expected = fmpq(0) if row is None else 1 + sum(
                (mass * h[j] for j, mass in row.items()), fmpq(0)
            )
            assert h[k] == expected, (model["n"], policy, p, k)
        initialized = sum(
            (weight * value for weight, value in zip(model["initial_weights"], h)),
            fmpq(0),
        )
        metadata.update(
            expected=str(initialized),
            expected_decimal=float(initialized),
            worst_state_expected=str(max(h)),
            rational_bellman_equations_checked=len(rows),
        )
        certificate["h"] = list(map(str, h))
        certificate["expected"] = str(initialized)
    metadata["solver_seconds"] = time.perf_counter() - started
    return metadata, certificate


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new evidence directory")
    args = parser.parse_args()
    if digest(HERE / "PROTOCOL.md") != PROTOCOL_SHA256:
        raise SystemExit("Protocol differs from the precomputation SHA-256.")
    bindings = [{"path": path, "sha256": digest(REPO / path)} for path in SOURCE_PATHS]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / "certificates").mkdir()
    result = {
        "schema_version": 1,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "protocol_sha256": PROTOCOL_SHA256,
        "bindings": bindings,
        "software": {
            "python": sys.version,
            "python_flint": flint.__version__,
            "platform": platform.platform(),
        },
        "initialization": "original uniform product; all arms identical",
        "cost": "resampling operations; initialization excluded",
        "barrier_policy": "p=1 if zero-based least failure i equals F, otherwise p=0",
        "static_grid": "p=k/12 for k=0,...,12; no global optimum certificate",
        "state_order": STATE_ORDER,
        "arms": [],
        "comparisons": [],
        "certificates": [],
        "status": "RUNNING",
    }
    started = time.perf_counter()
    for n in range(2, 6):
        if time.perf_counter() - started > 30 * 60:
            result["status"] = "BUDGET_EXHAUSTED"
            break
        model = build_model(n)
        arms = []
        for policy, p in [("static", fmpq(k, 12)) for k in range(13)] + [("barrier", None)]:
            metadata, certificate = solve(model, policy, p)
            tag = f"static-{str(p).replace('/', '_')}" if policy == "static" else "barrier"
            relative = f"certificates/n{n}-{tag}.json"
            certificate["protocol_sha256"] = PROTOCOL_SHA256
            write_json(output / relative, certificate)
            metadata["certificate"] = relative
            metadata["certificate_sha256"] = digest(output / relative)
            metadata["primary_arm"] = policy == "barrier" or p in (
                fmpq(1, 3), fmpq(2, 3), fmpq(1)
            )
            arms.append(metadata)
            result["arms"].append(metadata)
            result["certificates"].append({"path": relative, "sha256": digest(output / relative)})
            print(f"n={n} {tag}: {metadata['expected_decimal']}", flush=True)
        static = [arm for arm in arms if arm["policy"] == "static"]
        barrier = next(arm for arm in arms if arm["policy"] == "barrier")
        finite_static = [arm for arm in static if arm["expected"] != "infinite"]
        best = min(finite_static, key=lambda arm: fmpq(arm["expected"])) if finite_static else None
        witnesses = [
            arm["p"] for arm in finite_static
            if barrier["expected"] == "infinite" or fmpq(arm["expected"]) <= fmpq(barrier["expected"])
        ]
        result["comparisons"].append({
            "n": n,
            "best_tested_static_p": best["p"] if best else None,
            "best_tested_static_expected": best["expected"] if best else "infinite",
            "barrier_expected": barrier["expected"],
            "static_witnesses_no_worse_than_barrier": witnesses,
            "barrier_beats_global_best_static": False if witnesses else "not_certified",
            "global_static_optimizer_certified": False,
        })
    else:
        result["status"] = "COMPLETE"
    for binding in bindings:
        if digest(REPO / binding["path"]) != binding["sha256"]:
            raise RuntimeError(f"Input changed during computation: {binding['path']}")
    result["finished_utc"] = datetime.now(timezone.utc).isoformat()
    result["total_seconds"] = time.perf_counter() - started
    write_json(output / "RESULT.json", result)
    print(f"Wrote {output / 'RESULT.json'}", flush=True)


if __name__ == "__main__":
    main()
