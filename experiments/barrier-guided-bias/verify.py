#!/usr/bin/env python3
"""Read-only, stdlib-only verification of exact finite-chain certificates.

This implementation does not import the solver. In particular, it reconstructs
all 36 original raw draws, including the ignored fixed-endpoint draws, rather
than using the solver's compressed transition enumeration.
"""

import argparse
from collections import defaultdict, deque
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STATE_ORDER = "thresholds_lex_then_labels_lex;0=strong;1=weak"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inside(base, name):
    path = (base / name).resolve()
    require(path.is_relative_to(base.resolve()), "path escapes its evidence root")
    return path


def states(n):
    return list(product(product(range(3), repeat=n - 1),
                        product(range(2), repeat=n)))


def features(n, state):
    thresholds, labels = state
    values = (2,) + thresholds + (0,)
    passed = [(values[j] == values[j + 1] if labels[j] == 1
               else values[j + 1] <= values[j]) for j in range(n)]
    failed = [j for j in range(n) if not passed[j]]
    if not failed:
        return None, n
    height = 0
    prefix_passes = True
    for j in range(n):
        prefix_passes = prefix_passes and passed[j]
        if prefix_passes and values[j] == 2 and labels[j] == 0:
            height = j + 1
    require(height <= failed[0], "barrier exceeds zero-based least failure")
    return failed[0], height


def raw_successors(n, state, policy, p):
    selected, height = features(n, state)
    if selected is None:
        return {}
    if policy == "barrier":
        bias = Fraction(int(selected == height))
    else:
        require(policy == "static", "unrecognized policy")
        bias = Fraction(p)
    require(0 <= bias <= 1, "invalid probability")
    mass = [(1 - bias) / 2, (1 - bias) / 2, bias]
    output = defaultdict(Fraction)
    thresholds, labels = state
    for left, right, raw_label in product(range(3), range(3), range(4)):
        probability = mass[left] * mass[right] / 4
        if probability == 0:
            continue
        values = [2, *thresholds, 0]
        if selected != 0:
            values[selected] = left
        if selected + 1 != n:
            values[selected + 1] = right
        new_labels = list(labels)
        new_labels[selected] = int(raw_label == 1)
        successor = (tuple(values[1:-1]), tuple(new_labels))
        output[successor] += probability
    require(sum(output.values()) == 1, "transition mass is not one")
    return output


def check_vector(n, policy, p, vector, expected):
    catalog = states(n)
    require(len(vector) == len(catalog), "wrong Bellman vector length")
    h = dict(zip(catalog, map(Fraction, vector)))
    require(all(value >= 0 for value in h.values()), "negative Bellman value")
    predecessors = defaultdict(set)
    terminal = []
    active_count = 0
    for state in catalog:
        selected, _ = features(n, state)
        if selected is None:
            require(h[state] == 0, "Good state has nonzero cost")
            terminal.append(state)
            continue
        active_count += 1
        successors = raw_successors(n, state, policy, p)
        rhs = 1 + sum(probability * h[target]
                      for target, probability in successors.items())
        require(h[state] == rhs, f"Bellman residual at {state}")
        for target in successors:
            predecessors[target].add(state)
    reachable = set(terminal)
    queue = deque(terminal)
    while queue:
        for previous in predecessors[queue.popleft()]:
            if previous not in reachable:
                reachable.add(previous)
                queue.append(previous)
    require(len(reachable) == len(catalog), "closed active class detected")
    total_mass = Fraction(0)
    average = Fraction(0)
    for state in catalog:
        weak = sum(state[1])
        # Three raw strong labels per strong symbol, not uniform quotient mass.
        weight = Fraction(3 ** (n - weak), 3 ** (n - 1) * 4 ** n)
        total_mass += weight
        average += weight * h[state]
    require(total_mass == 1, "initialization mass is not one")
    require(average == Fraction(expected), "wrong initialized expectation")
    return {"states": len(catalog), "active": active_count,
            "expected": str(average), "all_states_reach_good": True}


def table_check():
    # Every raw label has exactly its original pass semantics after quotienting.
    checked = 0
    for a, b, raw_label in product(range(3), range(3), range(4)):
        raw_pass = a == b if raw_label == 1 else b <= a
        weak = int(raw_label == 1)
        quotient_pass = a == b if weak else b <= a
        require(raw_pass == quotient_pass, "raw-label quotient changes passes")
        checked += 1
    return checked


def verify(data):
    result = json.loads((data / "RESULT.json").read_text())
    require(result["schema_version"] == 1, "unsupported receipt schema")
    bound = {item["path"] for item in result["bindings"]}
    required = {
        "formal/mt/core/FreshDraws.lean", "formal/mt/core/Chain.lean",
        "formal/mt/core/Features.lean", "formal/mt/core/ChainKernel.lean",
        "research/biased-resampling/formal/BiasedDefinitions.lean",
        "experiments/barrier-guided-bias/PROTOCOL.md",
        "experiments/barrier-guided-bias/run.py",
        "experiments/barrier-guided-bias/verify.py",
    }
    require(required <= bound, "missing source or checker binding")
    for item in result["bindings"]:
        require(digest(inside(ROOT, item["path"])) == item["sha256"],
                f"changed bound source: {item['path']}")
    checked = []
    means = {}
    certificates = {}
    for arm in result["arms"]:
        path = inside(data, arm["certificate"])
        require(digest(path) == arm["certificate_sha256"], "changed certificate")
        certificate = json.loads(path.read_text())
        for field in ("n", "policy", "p"):
            require(certificate[field] == arm[field], "arm/certificate mismatch")
        require(certificate["state_order"] == STATE_ORDER, "wrong state order")
        key = (arm["n"], arm["policy"], arm["p"])
        require(key not in means, "duplicate arm")
        item = check_vector(*key, certificate["h"], arm["expected"])
        checked.append({"n": key[0], "policy": key[1], "p": key[2], **item})
        means[key] = Fraction(item["expected"])
        certificates[key] = certificate
    comparisons = []
    for n in range(2, 6):
        adaptive = means[(n, "barrier", None)]
        static = means[(n, "static", "1")]
        # The negative conclusion uses this witness, not an unproved optimizer.
        require(static < adaptive, "static witness no longer beats the policy")
        for p in ("1/3", "2/3"):
            require((n, "static", p) in means, "missing primary static arm")
        comparisons.append({"n": n, "adaptive_minus_static_p1":
                            str(adaptive - static)})
    # Exercise two failures of the same verifier without modifying evidence.
    key = (2, "barrier", None)
    original = certificates[key]
    corrupt = list(original["h"])
    first_active = next(j for j, state in enumerate(states(2))
                        if features(2, state)[0] is not None)
    corrupt[first_active] = str(Fraction(corrupt[first_active]) + Fraction(1, 1000))
    controls = []
    for name, vector, expected in (
        ("changed_active_value", corrupt, means[key]),
        ("changed_initial_average", original["h"], means[key] + 1),
    ):
        try:
            check_vector(2, "barrier", None, vector, expected)
        except ValueError as error:
            controls.append({"control": name, "rejected": True,
                             "reason": str(error)})
        else:
            raise ValueError(f"negative control unexpectedly accepted: {name}")
    return {"status": "PASS", "raw_table_cases": table_check(),
            "arms": checked, "comparisons": comparisons, "controls": controls,
            "new_lean_or_nanoda_proof": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=HERE / "evidence")
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.data.resolve()), indent=2))
    except (ValueError, KeyError, OSError) as error:
        print(json.dumps({"status": "FAIL", "reason": str(error)}))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
