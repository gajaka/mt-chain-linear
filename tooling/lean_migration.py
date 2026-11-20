"""Check the versioned Lean compatibility edits without rewriting old manifests.

Old extraction/module receipts continue to describe their original bytes.
The active migration binds both those bytes and each current replacement.
This is source provenance, not a proof of equivalence between Lean versions.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re


RECORD = "provenance/lean-4.37.0-rc1/MIGRATION.json"
TOOLCHAIN = "leanprover/lean4:v4.37.0-rc1"
MATHLIB = "31ce06eaadf4a200c0e1407c5f10953cf606b8f8"
BASE_COMMIT = "bb903c9b301a01e136842d7b72719d97d0625745"
BASE_INVENTORY_SHA256 = "cbb09e64ff86e09047608113c7f48c8bd3c7d62bc5409d5dd6c352899fba98a3"
CHECK_SOURCE_SHA256 = "d238969376d98e3c408487b31ae5b82f5cdefab6e8f03d0217071954e2e9a1fb"
PRIMITIVES = (
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
    "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk",
    "Char", "optParam", "autoParam", "semiOutParam", "outParam",
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def primitive_targets(source):
    data = Path(source).read_bytes()
    require(sha(data) == CHECK_SOURCE_SHA256, "Comparator source differs from the pinned release")
    body = data.decode().split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0]
    # String.mk is now preceded by an inline set_option in the upstream list.
    # Commented Nat.zero/Nat.succ entries must remain excluded.
    code = "\n".join(line.split("--", 1)[0] for line in body.splitlines())
    names = re.findall(r"``([A-Za-z0-9_.]+)", code)
    require(tuple(names) == PRIMITIVES, "Pinned comparator primitive inventory changed")
    return names


class Migration:
    def __init__(self, root):
        self.root = Path(root).absolute()
        self.paths = set()
        self.old = {}
        self.changes = {}
        record = self.file(RECORD)
        data = json.loads(record.read_text())
        require(data.get("schema_version") == 1, "Unknown Lean migration schema")
        require(data.get("baseline_commit") == BASE_COMMIT, "Wrong migration baseline")
        require(data.get("from_toolchain") == "leanprover/lean4:v4.35.0" and
                data.get("to_toolchain") == TOOLCHAIN and data.get("mathlib_revision") == MATHLIB,
                "Wrong migration toolchain pair")
        inventories = (data.get("changes"), data.get("unchanged_files"), data.get("added_files"))
        require(all(isinstance(rows, list) for rows in inventories), "Missing migration inventory")
        seen = set()
        for row in data["changes"]:
            name = row["path"]
            require(name not in seen, "Duplicate migration path: " + name)
            seen.add(name)
            current = self.file(name)
            before = self.file("provenance/lean-4.37.0-rc1/before/" + name)
            old, new = before.read_bytes(), current.read_bytes()
            require(sha(old) == row["before_sha256"] and sha(new) == row["after_sha256"],
                    "Changed migration input: " + name)
            text = old.decode("utf-8")
            edits = row.get("edits")
            require(isinstance(edits, list) and edits, "Missing exact compatibility edits")
            end = 0
            parts = []
            for edit in edits:
                start, stop = edit["start"], edit["end"]
                require(type(start) is int and type(stop) is int and
                        end <= start <= stop <= len(text), "Overlapping or invalid edit")
                require(text[start:stop] == edit["before"], "Compatibility edit origin differs")
                parts.extend((text[end:start], edit["after"]))
                end = stop
            parts.append(text[end:])
            require("".join(parts).encode("utf-8") == new,
                    "Unrecorded compatibility edit: " + name)
            self.old[name] = old
            self.changes[name] = row
        for key in ("unchanged_files", "added_files"):
            for row in data[key]:
                name = row["path"]
                require(name not in seen and name != RECORD, "Overlapping migration inventory")
                seen.add(name)
                require(sha(self.file(name).read_bytes()) == row["sha256"],
                        "Changed " + key + " input: " + name)
        baseline = [{"path": row["path"], "sha256": row["before_sha256"]}
                    for row in data["changes"]] + data["unchanged_files"]
        encoded = json.dumps(sorted(baseline, key=lambda row: row["path"]),
                             sort_keys=True, separators=(",", ":")).encode()
        require(len(baseline) == 482 and sha(encoded) == BASE_INVENTORY_SHA256,
                "Missing, substituted or unbound baseline inventory")
        require({"lean-toolchain", "lakefile.lean", "lake-manifest.json",
                 "scripts/provenance.py", "library/check.py"} <= self.changes.keys(),
                "Incomplete active toolchain migration")
        require("tooling/lean_migration.py" in {row["path"] for row in data["added_files"]},
                "Unbound migration validator")
        require(self.file("lean-toolchain").read_text().strip() == TOOLCHAIN,
                "Active Lean toolchain differs")
        for relative in ("lake-manifest.json", "library/lake-manifest.json",
                         "research/certificate-existence/lake-manifest.json",
                         "research/biased-resampling/lake-manifest.json"):
            packages = json.loads(self.file(relative).read_text())["packages"]
            selected = [p for p in packages if p["name"] == "mathlib"]
            require(len(selected) == 1 and selected[0]["rev"] == MATHLIB,
                    "Active Mathlib revision differs: " + relative)
        self.data = data

    def file(self, name):
        require(isinstance(name, str), "Invalid migration path")
        relative = PurePosixPath(name)
        require(name and not relative.is_absolute() and str(relative) == name and
                all(p not in {".", "..", ".git", ".lake"} for p in relative.parts),
                "Noncanonical migration path: " + name)
        path = self.root
        for part in relative.parts:
            path = path / part
            require(not path.is_symlink(), "Symlink in migration input: " + name)
        require(path.is_file() and path.resolve().is_relative_to(self.root.resolve()),
                "Missing or external migration input: " + name)
        self.paths.add(path)
        return path

    def baseline_bytes(self, name):
        name = str(name)
        if name in self.old:
            require(sha(self.file(name).read_bytes()) == self.changes[name]["after_sha256"],
                    "Active source changed during validation: " + name)
            return self.old[name]
        return self.file(name).read_bytes()

    def baseline_sha(self, name):
        return sha(self.baseline_bytes(name))

    def receipt(self):
        return {"status": "PASS", "record": RECORD, "record_sha256": sha(self.file(RECORD).read_bytes()),
                "from_toolchain": self.data["from_toolchain"], "to_toolchain": TOOLCHAIN,
                "mathlib_revision": MATHLIB, "exact_compatibility_changes": len(self.changes),
                "unchanged_baseline_files": len(self.data["unchanged_files"]),
                "scope": "Exact active compatibility edits and retained historical identities; not a kernel replay"}


if __name__ == "__main__":
    print(json.dumps(Migration(Path(__file__).resolve().parents[1]).receipt(), indent=2))
