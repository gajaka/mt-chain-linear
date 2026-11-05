"""Exact constructed counterexample to a raw-feature update factorization.

This is not a measured LUCES coupling. The four features are valid-row count,
mean row concentration, support-pair violations and support size. Two rational
10-bin couplings have equal features and equal uniform marginals, but the same
half-mixture with the diagonal coupling changes their concentrations differently.

The support/cycle tolerance here is exactly 1/10^10. This is a mathematical
rational model, not a claim of bitwise equivalence with NumPy/POT arithmetic.
Both output concentrations remain above the existing Monge cutoff, so this
particular pair does not demonstrate a changed Boolean Monge result.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


SIZE = 10
EPSILON = Fraction(1, 10**10)
UNIFORM_MASS = Fraction(1, 10)
MONGE_THRESHOLD = Fraction(1553741871442821, 2251799813685248)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    return {"numerator": value.numerator, "denominator": value.denominator}


def cost(i, j):
    return Fraction((i - j) ** 2, (SIZE - 1) ** 2)


def coupling(flipped):
    matrix = [[Fraction(0) for _ in range(SIZE)] for _ in range(SIZE)]
    diagonal, off_diagonal = (
        (Fraction(1, 100), Fraction(9, 100)) if flipped
        else (Fraction(9, 100), Fraction(1, 100))
    )
    matrix[0][0] = matrix[1][1] = diagonal
    matrix[0][1] = matrix[1][0] = off_diagonal
    for i in range(2, SIZE):
        matrix[i][i] = UNIFORM_MASS
    return matrix


def half_mix_diagonal(matrix):
    return [[(matrix[i][j] + (UNIFORM_MASS if i == j else 0)) / 2
             for j in range(SIZE)] for i in range(SIZE)]


def features(matrix):
    require(len(matrix) == SIZE and all(len(row) == SIZE for row in matrix),
            "Expected a 10 by 10 matrix")
    require(all(value >= 0 for row in matrix for value in row), "Negative mass")
    row_masses = [sum(row) for row in matrix]
    column_masses = [sum(matrix[i][j] for i in range(SIZE)) for j in range(SIZE)]
    require(row_masses == [UNIFORM_MASS] * SIZE, "Row marginals changed")
    require(column_masses == [UNIFORM_MASS] * SIZE, "Column marginals changed")
    valid = [i for i, mass in enumerate(row_masses) if mass > EPSILON]
    support = [(i, j) for i in range(SIZE) for j in range(SIZE)
               if matrix[i][j] > EPSILON]
    violations = sum(
        cost(i, j) + cost(k, ell) > cost(i, ell) + cost(k, j) + EPSILON
        for index, (i, j) in enumerate(support)
        for k, ell in support[index + 1:]
    )
    concentration = sum(max(matrix[i]) / row_masses[i] for i in valid) / len(valid)
    return (len(valid), concentration, violations, len(support))


def feature_record(values):
    rows, concentration, violations, nonzeros = values
    return {"valid_rows": rows, "monge_fraction": rational(concentration),
            "violations": violations, "nnz": nonzeros,
            "monge_boolean_at_original_threshold": concentration > MONGE_THRESHOLD}


def matrix_record(matrix):
    return [[rational(value) for value in row] for row in matrix]


def compute():
    first, second = coupling(False), coupling(True)
    first_after, second_after = half_mix_diagonal(first), half_mix_diagonal(second)
    before_a, before_b = features(first), features(second)
    after_a, after_b = features(first_after), features(second_after)
    require(before_a == before_b == (10, Fraction(49, 50), 1, 12),
            "Constructed input features do not agree")
    require(after_a == (10, Fraction(99, 100), 1, 12), "Unexpected output A")
    require(after_b == (10, Fraction(91, 100), 1, 12), "Unexpected output B")
    require(after_a != after_b, "No feature distinction after the common operation")
    require(after_a[1] > MONGE_THRESHOLD and after_b[1] > MONGE_THRESHOLD,
            "This example must not be presented as a changed Boolean Monge test")
    return {
        "status": "EXACT_RATIONAL_CHECK_PASS",
        "classification": "CONSTRUCTED_NOT_MEASURED",
        "arithmetic": "Python standard-library Fraction; exact rational model",
        "size": SIZE,
        "uniform_row_and_column_marginals": [rational(UNIFORM_MASS)] * SIZE,
        "support_and_cycle_tolerance": rational(EPSILON),
        "cost_formula": "(i-j)^2 / 81 for i,j in {0,...,9}",
        "cost_matrix": [[rational(cost(i, j)) for j in range(SIZE)] for i in range(SIZE)],
        "operation": "P -> (P + (1/10) I_10) / 2",
        "monge_threshold": rational(MONGE_THRESHOLD),
        "before": {
            "A": {"matrix": matrix_record(first), "features": feature_record(before_a)},
            "B": {"matrix": matrix_record(second), "features": feature_record(before_b)},
        },
        "after": {
            "A": {"matrix": matrix_record(first_after), "features": feature_record(after_a)},
            "B": {"matrix": matrix_record(second_after), "features": feature_record(after_b)},
        },
        "conclusion": "Equal current raw local features do not determine the next raw local features under this operation.",
        "scope_limits": [
            "Constructed uniform marginals, not any measured boot marginals or finite candidate bank",
            "No bitwise NumPy/POT arithmetic equivalence asserted",
            "Both output Monge predicates remain true at the original threshold",
            "No refutation of the protected GEN/dataset Fixed theorem",
            "No physical repair, runtime advantage, MT or scientific novelty claim",
        ],
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser()
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=Path)
    action.add_argument("--verify", type=Path)
    args = parser.parse_args()
    result = compute()
    if args.verify:
        require(json.loads(args.verify.read_text()) == result, "Saved result differs from exact reconstruction")
    else:
        with args.output.open("x") as stream:
            json.dump(result, stream, indent=2)
            stream.write("\n")
    print(json.dumps({"status": result["status"], "classification": result["classification"],
                      "before": result["before"]["A"]["features"],
                      "after_A": result["after"]["A"]["features"],
                      "after_B": result["after"]["B"]["features"]}, indent=2))


if __name__ == "__main__":
    main()
