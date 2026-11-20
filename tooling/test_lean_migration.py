"""Negative controls for current-source and historical-evidence admission."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from lean_migration import Migration, RECORD, TOOLCHAIN, primitive_targets


class MigrationControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = Path(__file__).resolve().parents[1]
        cls.directory = tempfile.TemporaryDirectory(prefix="mt-migration-controls-")
        cls.root = Path(cls.directory.name)
        migration = Migration(cls.source)
        cls.record = json.loads((cls.source / RECORD).read_text())
        for path in migration.paths:
            target = cls.root / path.relative_to(cls.source)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
        cls.proof = next(row for row in cls.record["changes"]
                         if row.get("kind") == "proof-compatibility")

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def setUp(self):
        self.saved = {}

    def replace(self, name, data):
        path = self.root / name
        self.saved.setdefault(path, path.read_bytes())
        path.write_bytes(data)

    def edit_record(self, data):
        self.replace(RECORD, json.dumps(data).encode())

    def tearDown(self):
        for path, data in self.saved.items():
            if path.is_symlink(): path.unlink()
            path.write_bytes(data)

    def test_valid_migration(self):
        self.assertEqual(Migration(self.root).receipt()["status"], "PASS")

    def test_unregistered_proof_escape(self):
        path = self.proof["path"]
        self.replace(path, (self.root / path).read_bytes() + b"\naxiom forged : False\n")
        with self.assertRaises(ValueError): Migration(self.root)

    def test_matching_hash_without_matching_edit_is_rejected(self):
        path = self.proof["path"]
        altered = (self.root / path).read_bytes() + b"\naxiom forged : False\n"
        self.replace(path, altered)
        record = copy.deepcopy(self.record)
        row = next(row for row in record["changes"] if row["path"] == path)
        row["after_sha256"] = hashlib.sha256(altered).hexdigest()
        self.edit_record(record)
        with self.assertRaises(ValueError): Migration(self.root)

    def test_retained_before_source_is_checked(self):
        name = "provenance/lean-4.37.0-rc1/before/" + self.proof["path"]
        self.replace(name, (self.root / name).read_bytes() + b"\n")
        with self.assertRaises(ValueError): Migration(self.root)

    def test_frozen_source_manifest_is_checked(self):
        self.replace("SOURCE_MANIFEST.json", b"{}\n")
        with self.assertRaises(ValueError): Migration(self.root)

    def test_cannot_drop_a_frozen_input_from_inventory(self):
        record = copy.deepcopy(self.record)
        row = record["unchanged_files"].pop()
        self.replace(row["path"], b"forged frozen evidence\n")
        self.edit_record(record)
        with self.assertRaises(ValueError): Migration(self.root)

    def test_path_traversal_is_rejected(self):
        record = copy.deepcopy(self.record)
        record["changes"][0]["path"] = "../outside"
        self.edit_record(record)
        with self.assertRaises(ValueError): Migration(self.root)

    def test_symlink_to_identical_bytes_is_rejected(self):
        name = self.proof["path"]
        path = self.root / name
        self.saved[path] = path.read_bytes()
        external = self.root / "identical-external-copy"
        external.write_bytes(path.read_bytes())
        path.unlink()
        path.symlink_to(external)
        try:
            with self.assertRaises(ValueError): Migration(self.root)
        finally:
            external.unlink()

    def test_other_toolchain_is_rejected(self):
        record = copy.deepcopy(self.record)
        record["to_toolchain"] = "leanprover/lean4:nightly"
        self.edit_record(record)
        with self.assertRaises(ValueError): Migration(self.root)

    def test_inline_primitive_is_retained(self):
        prefix = Path.home() / ".elan/toolchains" / TOOLCHAIN.replace("/", "--").replace(":", "---")
        names = primitive_targets(prefix / "src/lean/lake/Lake/CLI/Check.lean")
        self.assertEqual(len(names), 26)
        self.assertIn("String.mk", names)
        self.assertNotIn("Nat.zero", names)

    def test_altered_comparator_source_is_rejected(self):
        prefix = Path.home() / ".elan/toolchains" / TOOLCHAIN.replace("/", "--").replace(":", "---")
        altered = self.root / "altered-Check.lean"
        altered.write_bytes((prefix / "src/lean/lake/Lake/CLI/Check.lean").read_bytes() + b"\n")
        try:
            with self.assertRaises(ValueError): primitive_targets(altered)
        finally:
            altered.unlink()


if __name__ == "__main__":
    unittest.main()
