#!/usr/bin/env python3
"""Regression checks for the whole-library audit's rejection boundaries."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import audit_ppgraph as audit


class AuditTests(unittest.TestCase):
    def test_comments_strings_and_lean_identifiers(self):
        source = '''/- theorem fake : sorry /- axiom nested -/ -/
def text := "theorem fake native_decide"
@[simp] theorem Scope.answer' : True := by trivial
  theorem Scope.read?_step : True := by trivial
#check @Scope.answer'
#check @Scope.read?_step
-- #check @fake
'''
        declarations, checks = audit.inspect_source(source, "fixture")
        self.assertEqual(declarations, [("Scope.answer'", 3), ("Scope.read?_step", 4)])
        self.assertEqual(checks, ["Scope.answer'", "Scope.read?_step"])

    def test_missing_check_is_not_covered_by_an_import(self):
        entries = [{"name": "Local.proof", "kind": "theorem", "line": 1},
                   {"name": "Local.model", "kind": "definition", "line": 2}]
        names, missing = audit.missing_checks(
            [("proof", 1)], ["Imported.proof", "Local.model"], entries)
        self.assertEqual(names, ["Local.proof"])
        self.assertEqual(missing, ["Local.proof"])
        self.assertEqual(audit.missing_checks(
            [("proof", 1)], ["Local.proof"], entries)[1], [])

    def test_unapproved_source_mechanisms_are_rejected(self):
        for mechanism in ("sorry", "admit", "native_decide", "bv_decide"):
            with self.subTest(mechanism=mechanism), self.assertRaises(AssertionError):
                audit.inspect_source(f"theorem x : True := by {mechanism}\n", "fixture")
        for source in ("axiom x : True\n", "#print axioms x\n",
                       "unsafe def x : Nat := 0\n",
                       '@[extern "foreign"] def x : Nat := 0\n',
                       "@[implemented_by replacement] def x : Nat := 0\n"):
            with self.subTest(source=source), self.assertRaises(AssertionError):
                audit.inspect_source(source, "fixture")

    def test_any_allowed_subset_and_apostrophes(self):
        raw = ("'proof' does not depend on any axioms\n"
               "'Scope.answer'' depends on axioms: [propext,\nQuot.sound]\n"
               "'other' depends on axioms: [Classical.choice]\n")
        result = audit.dependencies_from_output(raw, ["proof", "Scope.answer'", "other"])
        self.assertEqual(result["proof"], [])
        self.assertEqual(result["Scope.answer'"], ["Quot.sound", "propext"])

    def test_unapproved_incomplete_and_duplicate_dependencies(self):
        for raw in (
            "'proof' depends on axioms: [sorryAx]\n",
            "'proof' depends on axioms: [CompilerCorrectness]\n",
            "",
            "'proof' does not depend on any axioms\n" * 2,
        ):
            with self.subTest(raw=raw), self.assertRaises(AssertionError):
                audit.dependencies_from_output(raw, ["proof"])

    def test_unreferenced_project_axioms_are_rejected(self):
        with self.assertRaisesRegex(AssertionError, "project-owned axiom"):
            audit.inventory_from_output(
                "PPG_INVENTORY|PPGraphFixture|unused|axiom|1\n",
                ["PPGraphFixture"])

    def test_nested_modules_with_duplicate_basenames_keep_their_owners(self):
        modules = ["PPGraph.Shearer.Expectation", "PPGraph.MoserTardos.Expectation"]
        output = ("PPG_INVENTORY|PPGraph.Shearer.Expectation|Shearer.result|theorem|2\n"
                  "PPG_INVENTORY|PPGraph.MoserTardos.Expectation|MT.result|theorem|3\n")
        inventory = audit.inventory_from_output(output, modules)
        self.assertEqual(inventory[modules[0]][0]["name"], "Shearer.result")
        self.assertEqual(inventory[modules[1]][0]["name"], "MT.result")

    def test_missing_and_unknown_canonical_owners_are_rejected(self):
        for output in (
            "PPG_INVENTORY|PPGraph.Core.Graph|Core.result|theorem|1\n",
            "PPG_INVENTORY|PPGraph.Other|Other.result|theorem|1\n",
        ):
            with self.subTest(output=output), self.assertRaises(AssertionError):
                audit.inventory_from_output(output,
                    ["PPGraph.Core.Graph", "PPGraph.Core.Repair"])

    def test_declared_import_only_facades_may_have_no_owned_declarations(self):
        output = "PPG_INVENTORY|PPGraph.Core.Graph|Core.result|theorem|1\n"
        inventory = audit.inventory_from_output(output,
            ["PPGraph.Core.Graph"], ["PPGraph", "PPGraph.All"])
        self.assertEqual(set(inventory), {"PPGraph.Core.Graph"})
        with self.assertRaisesRegex(AssertionError, "missing modules"):
            audit.inventory_from_output(output, ["PPGraph.Core.Graph", "PPGraph.All"])

    def test_facade_owned_axioms_and_other_declarations_are_rejected(self):
        output = "PPG_INVENTORY|PPGraph.Core.Graph|Core.result|theorem|1\n"
        for kind, message in (("axiom", "project-owned axiom"),
                              ("definition", "import-only facade owns")):
            with self.subTest(kind=kind), self.assertRaisesRegex(AssertionError, message):
                audit.inventory_from_output(output +
                    f"PPG_INVENTORY|PPGraph.All|unused|{kind}|1\n",
                    ["PPGraph.Core.Graph"], ["PPGraph.All"])


class ModuleMapTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="ppg-audit-map-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.manifest = {
            "schema_version": 1,
            "canonical_modules": [
                {"old_path": "PPGraphShearerExpectation.lean",
                 "path": "PPGraph/Shearer/Expectation.lean",
                 "module": "PPGraph.Shearer.Expectation"},
                {"old_path": "PPGraphMoserTardosExpectation.lean",
                 "path": "PPGraph/MoserTardos/Expectation.lean",
                 "module": "PPGraph.MoserTardos.Expectation"}],
            "facades": [{"path": "PPGraph.lean", "module": "PPGraph"},
                        {"path": "PPGraph/All.lean", "module": "PPGraph.All"}],
        }
        for row in self.manifest["canonical_modules"] + self.manifest["facades"]:
            path = self.root / row["path"]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- fixture\n")
        (self.root / "tools").mkdir()
        (self.root / "lakefile.lean").write_text(
            'lean_lib PPGraph where\n  srcDir := "."\n'
            '  roots := #[`PPGraph]\n  globs := #[.andSubmodules `PPGraph]\n')
        self.write_manifest()

    def write_manifest(self):
        (self.root / "tools/module-map.json").write_text(json.dumps(self.manifest))

    def test_recursive_map_and_lake_configuration(self):
        canonical, facades = audit.load_module_map(self.root)
        self.assertEqual(set(canonical),
            {"PPGraph.Shearer.Expectation", "PPGraph.MoserTardos.Expectation"})
        self.assertEqual(set(facades), {"PPGraph", "PPGraph.All"})
        audit.validate_lake_configuration(self.root)

    def test_unknown_and_missing_source_files_are_rejected(self):
        unknown = self.root / "PPGraph/Unmapped.lean"
        unknown.write_text("-- unlisted\n")
        with self.assertRaisesRegex(AssertionError, "unknown=.*Unmapped"):
            audit.load_module_map(self.root)
        unknown.unlink()
        (self.root / "PPGraph/Shearer/Expectation.lean").unlink()
        with self.assertRaisesRegex(AssertionError, "missing=.*Shearer/Expectation"):
            audit.load_module_map(self.root)

    def test_duplicate_and_inconsistent_module_paths_are_rejected(self):
        row = self.manifest["canonical_modules"][0]
        self.manifest["canonical_modules"].append(dict(row))
        self.write_manifest()
        with self.assertRaisesRegex(AssertionError, "duplicate module-map"):
            audit.load_module_map(self.root)
        self.manifest["canonical_modules"].pop()
        row["module"] = "PPGraph.Wrong.Expectation"
        self.write_manifest()
        with self.assertRaisesRegex(AssertionError, "module/path mismatch"):
            audit.load_module_map(self.root)

    def test_facade_source_is_still_checked_for_forbidden_mechanisms(self):
        canonical, facades = audit.load_module_map(self.root)
        for source in ("axiom unused : True\n", "theorem falseProof : False := by sorry\n"):
            (self.root / "PPGraph/All.lean").write_text(source)
            with self.subTest(source=source), self.assertRaises(AssertionError):
                audit.inspect_library_sources(canonical, facades)

    def test_nonrecursive_lake_glob_is_rejected(self):
        (self.root / "lakefile.lean").write_text(
            'lean_lib PPGraph where\n  roots := #[`PPGraph]\n'
            '  -- globs := #[.andSubmodules `PPGraph]\n')
        with self.assertRaisesRegex(AssertionError, "recursively build"):
            audit.validate_lake_configuration(self.root)


class IncludedInputTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="ppg-input-audit-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "data").mkdir()
        self.source = self.root / "src/Test.lean"
        self.asset = self.root / "data/input.json"
        self.asset.write_text('{"value": 1}\n')

    def test_literal_inputs_comments_and_elaborator_antiquotation(self):
        self.source.write_text('''-- include_str "missing.json"
def text := "include_ascii_bytes"
def value := include_str "../data/input.json"
def bytes := include_ascii_bytes "../data/input.json"
def elaborator := `(include_ascii_bytes $path:str)
''')
        self.assertEqual(audit.included_inputs([self.source], self.root),
                         {self.source: [self.asset.resolve()]})

    def test_missing_and_outside_inputs_are_rejected(self):
        for name in ("missing.json", "../../outside.json"):
            self.source.write_text(f'def value := include_str "{name}"\n')
            with self.subTest(name=name), self.assertRaisesRegex(
                    AssertionError, "missing/outside-project"):
                audit.included_inputs([self.source], self.root)

    def test_input_mutation_is_detected(self):
        hashes = {"data/input.json": audit.digest(self.asset)}
        audit.assert_hashes_unchanged(hashes, self.root)
        self.asset.write_text('{"value": 2}\n')
        with self.assertRaisesRegex(AssertionError, "source/input changed"):
            audit.assert_hashes_unchanged(hashes, self.root)


if __name__ == "__main__":
    unittest.main(verbosity=2)
