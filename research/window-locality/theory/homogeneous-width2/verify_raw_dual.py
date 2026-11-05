#!/usr/bin/env python3
"""Independently verify the rational bulk dual with the original 36 draws.

No solver, NumPy, or saved sparse-row coefficients are used. The rows are
rebuilt from six actual shared thresholds and five tactic profiles. Strong
old labels are independently averaged over raw labels 0, 2, 3. This justifies
lifting the profile identity to arbitrary original four-label window tables.
The check proves a local finite linear identity, not an all-n budget theorem.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import time


def pass_raw(a, b, r):
    return a == b if r == 1 else b <= a


def options(profile):
    return (1,) if profile == 1 else (0, 2, 3)


def encode(a, b, c, l, r):
    return ((((a * 3 + b) * 3 + c) * 4 + l) * 4 + r)


def profile_index(a, b, c, l, r):
    return ((((a * 3 + b) * 3 + c) * 2 + l) * 2 + r)


def verify(path):
    started = time.monotonic()
    original = path.read_bytes()
    data = json.loads(original)
    support = data['support']
    assert support and len(support) == 91
    weights = [Fraction(row['weight_exact']) for row in support]
    assert all(w > 0 for w in weights)
    assert sum(weights) == 1
    computed = [[Fraction(0) for _ in range(432)] for _ in range(4)]
    for weight, row in zip(weights, support):
        x, profiles = row['stencil']
        assert len(x) == 6 and all(type(a) is int and 0 <= a < 3 for a in x)
        assert len(profiles) == 5 and all(type(r) is int and r in (0, 1) for r in profiles)
        # Each possible original label must satisfy the actual pass predicate.
        assert all(pass_raw(x[0], x[1], r) for r in options(profiles[0]))
        assert all(pass_raw(x[1], x[2], r) for r in options(profiles[1]))
        assert all(not pass_raw(x[2], x[3], r) for r in options(profiles[2]))
        for k in range(4):
            component = defaultdict(Fraction)
            old_labels = list(itertools.product(options(profiles[k]), options(profiles[k + 1])))
            for l, r in old_labels:
                old_key = encode(x[k], x[k + 1], x[k + 2], l, r)
                component[old_key] += Fraction(1, len(old_labels))
                # Exactly 3 * 3 * 4 = 36 original equally likely redraws.
                for a, b, new_r in itertools.product(range(3), range(3), range(4)):
                    changed = list(x)
                    changed[2], changed[3] = a, b
                    next_l = new_r if k == 2 else l
                    next_r = new_r if k + 1 == 2 else r
                    next_key = encode(changed[k], changed[k + 1], changed[k + 2], next_l, next_r)
                    component[next_key] -= Fraction(1, 36 * len(old_labels))
            assert sum(component.values()) == 0
            for j, coefficient in component.items():
                computed[k][j] += weight * coefficient
    saved = [[Fraction(v) for v in component] for component in data['window_functionals']]
    assert len(saved) == 4 and all(len(c) == 108 for c in saved)
    for k in range(4):
        for a, b, c, l, r in itertools.product(range(3), range(3), range(3), range(4), range(4)):
            ql, qr = int(l == 1), int(r == 1)
            lifted = saved[k][profile_index(a, b, c, ql, qr)] / (len(options(ql)) * len(options(qr)))
            assert computed[k][encode(a, b, c, l, r)] == lifted
    assert all(sum(computed[k][j] for k in range(4)) == 0 for j in range(432))
    assert all(abs(v) <= 1 for component in computed for v in component)
    assert all(abs(computed[0][j] + computed[1][j]) <= 2 for j in range(432))
    assert all(abs(sum(computed[k][j] for k in range(3))) <= 1 for j in range(432))
    return {
        'status': 'PASS',
        'scope': 'exact local bulk identity, with original four-label tables and original 36 redraws',
        'dual_sha256': hashlib.sha256(original).hexdigest(),
        'support_rows': len(support),
        'positive_weight_sum': '1',
        'raw_columns': 432,
        'window_functionals': 4,
        'coefficient_sum_each_column': '0',
        'individual_coefficient_abs_bound': '1',
        'flux_cumulative_coefficient_abs_bounds': ['1', '2', '1'],
        'solver_status_trusted': False,
        'saved_sparse_rows_trusted': False,
        'elapsed_seconds': time.monotonic() - started,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('dual', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.dual)
    text = json.dumps(result, indent=2) + '\n'
    if args.output is not None:
        args.output.write_text(text)
    print(text, end='')
