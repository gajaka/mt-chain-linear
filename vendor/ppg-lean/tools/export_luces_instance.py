#!/usr/bin/env python3
"""Export exact observed runner inputs for the Lean certificate instance."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIELDS = [('valid_rows', 'validRows'), ('monge_fraction', 'mongeFraction'),
          ('violations', 'violations'), ('nnz', 'nnz'),
          ('generator_cos', 'generatorCos'), ('dataset_key', 'datasetKey')]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def ratio(value):
    q = Fraction(value) if isinstance(value, int) else Fraction.from_float(value)
    return [q.numerator, q.denominator]


def literal(pair):
    return f'({pair[0]} / {pair[1]} : ℚ)'


def outputs(runner):
    schema_path = runner / 'cert_runner/contracts/local_plan.json'
    bank_path = runner / 'cert_runner/contracts/boot320_plan_candidates.json'
    schema = json.loads(schema_path.read_text())
    binding = json.loads(bank_path.read_text())
    assert binding['contract_sha256'] == digest(schema_path)
    assert digest(runner / binding['source_csv']) == binding['source_csv_sha256']
    for name, expected in binding['producer_sha256'].items():
        assert digest(runner / name) == expected, name
    rows = [[ratio(state['snapshot'][field]) for field, _ in FIELDS]
            for state in binding['states']]
    kernel = {'schema_version': 1, 'source_csv_sha256': binding['source_csv_sha256'],
              'contract_sha256': binding['contract_sha256'], 'fields': [f for f, _ in FIELDS],
              'snapshots': rows, 'selected_position': 4}
    base = []
    names = dict(FIELDS)
    for check in schema['certificates']:
        field, bound = names[check['field']], literal(check['bound'])
        op = check['op']
        if op == 'gt': term = f'.neg (.atom .le .{field} {bound})'
        elif op in ('le', 'eq'): term = f'.atom .{op} .{field} {bound}'
        else: raise ValueError('unsupported check operation')
        base.append(term)
    kernel_bytes = (json.dumps(kernel, separators=(',', ':')) + '\n').encode()
    lines = ['/- Generated exact numeric inputs from the measured boot320 candidate bank.',
             '   Reproduce with python3 tools/export_luces_instance.py --runner-root ../master-controler.',
             '   Feature extraction is checked numerically in the runner; these are exact binary64 ratios. -/',
             '', 'module', '', 'public import PPGraph.Integration.FiniteReadCertificates',
             '', '@[expose] public section', '', 'namespace LucesObservedInputs', '',
             'open FiniteReadCertificates', '', 'inductive Field where',
             '  | validRows | mongeFraction | violations | nnz | generatorCos | datasetKey',
             '  deriving DecidableEq, Repr', '',
             'instance : Fintype Field where',
             '  elems := {.validRows, .mongeFraction, .violations, .nnz, .generatorCos, .datasetKey}',
             '  complete := by intro field; cases field <;> simp', '',
             'def Field.position : Field → ℕ',
             *[f'  | .{name} => {i}' for i, (_, name) in enumerate(FIELDS)], '',
             f'def datasetKey : ℚ := {binding["dataset_key"]}', '',
             f'def sourceCsvSHA256 : String := "{binding["source_csv_sha256"]}"', '',
             'def contractSource : String := include_str "../../artifacts/luces/local_plan.json"', '',
             'def kernelInputsSource : String := include_str "../../artifacts/luces/local_plan_kernel_inputs.json"', '',
             'def contractBytes : List Nat := [' + ', '.join(str(b) for b in schema_path.read_bytes()) + ']', '',
             'def kernelBytes : List Nat := [' + ', '.join(str(b) for b in kernel_bytes) + ']', '',
             'def baseChecks : List (Check Field) :=', '  [' + ',\n   '.join(base) + ']', '',
             'def snapshotRows : List (List ℚ) :=',
             '  [' + ',\n   '.join('[' + ', '.join(literal(q) for q in row) + ']' for row in rows) + ']', '',
             'def stateOfRow (row : List ℚ) (field : Field) : ℚ := row[field.position]?.getD 0', '',
             'def bank : List (Field → ℚ) := snapshotRows.map stateOfRow', '',
             'def before : Field → ℚ := stateOfRow snapshotRows[0]!', '',
             'def after : Field → ℚ := stateOfRow snapshotRows[4]!', '',
             'end LucesObservedInputs', '']
    row_text = binding['source_csv_sha256'] + '\n' + '\n'.join(' '.join(f'{q[0]}/{q[1]}' for q in row) for row in rows) + '\n'
    return {ROOT / 'artifacts/luces/local_plan.json': schema_path.read_bytes(),
            ROOT / 'artifacts/luces/local_plan_kernel_inputs.txt': row_text.encode(),
            ROOT / 'artifacts/luces/local_plan_kernel_inputs.json': (json.dumps(kernel, separators=(',', ':')) + '\n').encode(),
            ROOT / 'PPGraph/Integration/LucesObservedInputs.lean': '\n'.join(lines).encode()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner-root', type=Path, default=ROOT.parent / 'master-controler')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = outputs(args.runner_root.resolve())
    for path, content in expected.items():
        if args.check:
            assert path.read_bytes() == content, f'stale generated input: {path}'
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
    print('Verified' if args.check else 'Exported', len(expected), 'exact LUCES instance inputs')


if __name__ == '__main__':
    main()
