#!/usr/bin/env python3
"""Independent exact window-certificate checker, using only the standard library.

No solver, diagnostic matrix, or window_lp module is imported. Raw redraws,
features, initial masses, and every supported dual row are rebuilt here.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
import hashlib
from itertools import product
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT.parents[1]
DRAWS = tuple(product(range(3), range(3), range(4)))
PINNED_CORE = {
    "formal/mt/core/Chain.lean":
        "551779df094e539792ed5256078615c73d1fe1733ae83dd6b1fff5a30ab24a1d",
    "formal/mt/core/FreshDraws.lean":
        "c5b46028ba195cfd0d280b14933a999ebbb6b177feb4b4ce130788d06d2bdb9e",
    "formal/mt/core/ChainKernel.lean":
        "ba155ace55634b928b4a1a19fbd4e1c9d9a6ab9102462d8cceb219901529f6d2",
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    def nonfinite(value):
        raise ValueError("Nonfinite JSON number: " + value)
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object,
                      parse_constant=nonfinite)


def rational(value):
    require(type(value) is str, "Expected an exact rational string")
    return Q(value)


def integer_list(value, length, upper, label):
    require(type(value) is list and len(value) == length, "Wrong " + label + " length")
    require(all(type(x) is int and 0 <= x < upper for x in value),
            "Invalid " + label + " value")
    return tuple(value)


def canonical_variables(n, width):
    variables = [{"kind": "offset"}]
    for start in range(n - width + 1):
        for thresholds in product(range(3), repeat=width + 1):
            if start == 0 and thresholds[0] != 2:
                continue
            if start + width == n and thresholds[-1] != 0:
                continue
            for weak in product(range(2), repeat=width):
                variables.append({"kind": "window", "i": start,
                                  "thresholds": list(thresholds), "weak": list(weak)})
    return variables


def first_failure(state):
    thresholds, weak = state
    return next((i for i, flag in enumerate(weak)
                 if not (thresholds[i] == thresholds[i + 1] if flag == 1
                         else thresholds[i + 1] <= thresholds[i])), None)


def redraw(state, selected, draw):
    thresholds, weak = map(list, state)
    n = len(weak)
    incoming, outgoing, label = draw
    if selected > 0:
        thresholds[selected] = incoming
    if selected + 1 < n:
        thresholds[selected + 1] = outgoing
    weak[selected] = int(label == 1)
    return tuple(thresholds), tuple(weak)


def local_symmetry_checks():
    checked = 0
    for a, b, label in DRAWS:
        representative = 1 if label == 1 else 0
        raw_pass = a == b if label == 1 else b <= a
        profile_pass = a == b if representative == 1 else b <= a
        require(raw_pass == profile_pass, "Raw pass/profile disagreement")
        checked += 1
    counts = Counter((a, b, int(label == 1)) for a, b, label in DRAWS)
    require(all(counts[a, b, 0] == 3 and counts[a, b, 1] == 1
                for a, b in product(range(3), repeat=2)), "Changed profile draw weights")
    return checked


def verify(certificate, max_profiles=1000000):
    n, width = certificate["n"], certificate["width"]
    require(type(n) is int and n >= 2, "Invalid chain length")
    require(type(width) is int and 1 <= width <= n, "Invalid window width")
    expected_profiles = 3 ** (n - 1) * 2 ** n
    require(expected_profiles <= max_profiles, "Profile enumeration exceeds verifier resource cap")
    denominator = 3 ** (n - 1) * 4 ** n
    require(type(certificate["objective_denominator"]) is int and
            certificate["objective_denominator"] == denominator,
            "Wrong original initial-law denominator")
    variables = canonical_variables(n, width)
    require(type(certificate["variables"]) is list, "Variable inventory is not a list")
    for entry in certificate["variables"]:
        require(type(entry) is dict, "Malformed feature coordinate")
        if entry.get("kind") == "window":
            require(type(entry["i"]) is int, "Invalid window start index")
            integer_list(entry["thresholds"], width + 1, 3, "window threshold")
            integer_list(entry["weak"], width, 2, "window weak flag")
    require(certificate["variables"] == variables,
            "Variable inventory is not the complete canonical window class")
    coefficients = list(map(rational, certificate["primal"]))
    require(len(coefficients) == len(variables), "Wrong primal coefficient count")
    reported_objective = rational(certificate["objective"])
    require(type(certificate["dual"]) is list and certificate["dual"], "Empty dual support")

    support = []
    for entry in certificate["dual"]:
        middle = integer_list(entry["thresholds"], n - 1, 3, "dual threshold")
        weak = integer_list(entry["weak"], n, 2, "dual weak flag")
        require(entry["kind"] in ("drift", "nonnegative"), "Unknown dual row kind")
        weight = rational(entry["weight"])
        require(weight >= 0, "Negative dual multiplier")
        support.append((((2,) + middle + (0,), weak), entry["kind"], weight))

    index = {(entry["i"], tuple(entry["thresholds"]), tuple(entry["weak"])): j
             for j, entry in enumerate(variables) if entry["kind"] == "window"}

    def features(state, selected):
        if selected is None:
            return ()
        thresholds, weak = state
        return (0,) + tuple(index[start, thresholds[start:start + width + 1],
                                   weak[start:start + width]]
                            for start in range(n - width + 1))

    values, feature_rows, selected_sites = {}, {}, {}
    objective_numerators = [0] * len(variables)
    counts = Counter()
    direct_budget_numerator = Q(0)
    initial_bad_numerator = 0
    minimum_value = None
    for middle in product(range(3), repeat=n - 1):
        for weak in product(range(2), repeat=n):
            state = ((2,) + middle + (0,), weak)
            selected = first_failure(state)
            row = features(state, selected)
            value = sum((coefficients[j] for j in row), Q(0))
            require(value >= 0, "Negative whole stopped potential")
            mass = 3 ** weak.count(0)
            counts["profiles"] += 1
            counts["raw_mass"] += mass
            if selected is None:
                counts["good_profiles"] += 1
                counts["good_raw_mass"] += mass
                require(value == 0 and not row, "Nonzero terminal potential")
            else:
                counts["active_profiles"] += 1
                counts["active_raw_mass"] += mass
                minimum_value = value if minimum_value is None else min(minimum_value, value)
            thresholds = state[0]
            initial_bad_numerator += mass * sum(
                not (thresholds[i] == thresholds[i + 1] if flag == 1
                     else thresholds[i + 1] <= thresholds[i]) for i, flag in enumerate(weak))
            values[state], feature_rows[state], selected_sites[state] = value, row, selected
            direct_budget_numerator += mass * value
            for j in row:
                objective_numerators[j] += mass
    require(counts["profiles"] == expected_profiles and counts["raw_mass"] == denominator,
            "Incomplete state enumeration or wrong initial masses")
    require(counts["good_raw_mass"] + counts["active_raw_mass"] == denominator,
            "Good/active initial masses do not normalize")
    require(Q(initial_bad_numerator, denominator) == Q(5 * n - 6, 12),
            "Initial bad-event moment disagrees with the registered chain")
    objective = [Q(x, denominator) for x in objective_numerators]
    primal_value = sum((x * y for x, y in zip(objective, coefficients)), Q(0))
    require(primal_value == direct_budget_numerator / denominator == reported_objective,
            "Independent initial objective mismatch")

    minimum_drift = None
    for state, current in values.items():
        selected = selected_sites[state]
        if selected is None:
            continue
        next_sum = sum((values[redraw(state, selected, draw)] for draw in DRAWS), Q(0))
        scaled_drift = 36 * current - next_sum
        require(scaled_drift >= 36, "Raw pointwise drift is less than one")
        drift = scaled_drift / 36
        minimum_drift = drift if minimum_drift is None else min(minimum_drift, drift)
        counts["raw_draw_evaluations"] += 36

    total = [Q(0)] * len(variables)
    lower, weighted_slack = Q(0), Q(0)
    positive_rows = 0
    for state, kind, weight in support:
        require(state in values and selected_sites[state] is not None,
                "Dual row is not an active registered state")
        current = feature_rows[state]
        if kind == "nonnegative":
            row, rhs = Counter({j: 1 for j in current}), 0
        else:
            row, rhs = Counter({j: 36 for j in current}), 36
            for draw in DRAWS:
                for j in feature_rows[redraw(state, selected_sites[state], draw)]:
                    row[j] -= 1
        for j, coefficient in row.items():
            total[j] += weight * coefficient
        lower += weight * rhs
        slack = sum((Q(coefficient) * coefficients[j] for j, coefficient in row.items()), Q(0)) - rhs
        require(slack >= 0, "Primal violates a regenerated dual support row")
        weighted_slack += weight * slack
        positive_rows += weight > 0
    require(total == objective, "Dual identity A^T*y=c fails in the original feature space")
    gap = primal_value - lower
    require(gap >= 0 and weighted_slack == gap, "Exact weak-duality/slack identity failed")
    objective_bytes = json.dumps(list(map(str, objective)), separators=(",", ":")).encode()
    return {"status": "EXACT_OPTIMUM" if gap == 0 else "EXACT_BOUNDS",
            "n": n, "width": width, "feature_count": len(variables),
            "primal_objective": str(primal_value), "dual_objective": str(lower),
            "gap": str(gap), "minimum_value": str(minimum_value),
            "minimum_drift": str(minimum_drift), "counts": dict(counts),
            "dual_support_rows": len(support), "positive_dual_support_rows": positive_rows,
            "dual_identity_columns_checked": len(variables),
            "initial_objective_sha256": hashlib.sha256(objective_bytes).hexdigest(),
            "raw_state_coverage": "Exact profile symmetry, with all 36 raw redraws per active profile",
            "all_length_claim": False, "lean_checked": False, "nanoda_checked": False,
            "trust": "Independent standard-library Fraction certificate check; no optimizer imported"}


def negative_controls(certificate, max_profiles):
    broken = deepcopy(certificate)
    broken["primal"] = ["0"] * len(broken["primal"])
    broken["objective"] = "0"
    controls = [("zero primal", broken)]
    broken = deepcopy(certificate)
    for entry in broken["dual"]:
        entry["weight"] = "0"
    controls.append(("zero dual", broken))
    broken = deepcopy(certificate)
    broken["variables"] = broken["variables"][:-1]
    broken["primal"] = broken["primal"][:-1]
    controls.append(("omitted feature coordinate", broken))
    result = []
    for label, changed in controls:
        try:
            verify(changed, max_profiles)
        except ValueError as error:
            result.append({"control": label, "rejected": True, "reason": str(error)})
        else:
            raise ValueError("Negative control accepted: " + label)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--negative-controls", action="store_true")
    parser.add_argument("--max-profiles", type=int, default=1000000)
    args = parser.parse_args()
    started = time.monotonic()
    for path, expected in PINNED_CORE.items():
        require(digest(CORE / path) == expected, "Changed registered raw semantics: " + path)
    certificate = read_json(args.certificate)
    result = verify(certificate, args.max_profiles)
    result.update(certificate_sha256=digest(args.certificate),
                  verifier_sha256=digest(Path(__file__)),
                  specification_sha256=digest(ROOT / "SPEC.md"),
                  pinned_core_sources=PINNED_CORE,
                  raw_pass_symmetry_checks=local_symmetry_checks())
    if args.negative_controls:
        result["negative_controls"] = negative_controls(certificate, args.max_profiles)
    result["seconds"] = time.monotonic() - started
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as stream:
            json.dump(result, stream, indent=2, sort_keys=True)
            stream.write("\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, ZeroDivisionError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error)}))
        sys.exit(1)
