#!/usr/bin/env python3
"""Read-only source identity and import-closure check for the original library."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
SOURCE_COMMIT = "60151677e58704ce856c05a572904d681fd959f6"
MATHLIB_REVISION = "56a005855ea17e0b0958f73ec801ae140b0a1679"
REPAIR_ROOTS = {
    "PPGraph.Repair.Hazards", "PPGraph.Repair.SemanticHazards",
    "PPGraph.Repair.ObservableAlgebra", "PPGraph.Repair.ObservableKernel",
}
IMPORT = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+"
    r"([A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(source=None):
    manifest = json.loads((ROOT / "SOURCES.json").read_text())
    need(manifest["schema_version"] == 1, "Unknown source manifest schema")
    need(manifest["source_project"] == "ppg-lean", "Wrong source project")
    need(manifest["source_commit"] == SOURCE_COMMIT, "Wrong source revision")
    rows = manifest["files"]
    need(len(rows) == manifest["source_modules"] == 63, "Wrong module count")
    modules = {}
    paths = set()
    for row in rows:
        module = row["module"]
        path = "/".join(module.split(".")) + ".lean"
        need(module.startswith("PPGraph.") and row["path"] == path,
             "Unexpected source module path")
        need(module not in modules and path not in paths, "Duplicate source")
        file = ROOT / path
        need(not file.is_symlink() and file.is_file(), "Missing copied source")
        need(file.stat().st_size == row["bytes"] and digest(file) == row["sha256"],
             "Copied source changed: " + path)
        modules[module] = file
        paths.add(path)
    actual = {p.relative_to(ROOT).as_posix()
              for p in (ROOT / "PPGraph").rglob("*.lean")}
    need(actual == paths, "Missing or extra PPGraph source files")
    mt = {m for m in modules if m.startswith("PPGraph.MoserTardos.")}
    need(len(mt) == manifest["moser_tardos_modules"] == 44, "Wrong MT inventory")
    roots = manifest["roots"]
    need(len(roots) == len(set(roots)) and set(roots) == mt | REPAIR_ROOTS,
         "Unexpected selected roots")
    visited = set()

    def visit(module):
        if module in visited:
            return
        need(module in modules, "Missing local dependency: " + module)
        visited.add(module)
        for imported in IMPORT.findall(modules[module].read_text()):
            if imported.startswith("PPGraph"):
                visit(imported)
            else:
                need(imported.split(".")[0] in {"Mathlib", "Lean", "Std", "Init"},
                     "Unexpected external dependency: " + imported)

    for module in roots:
        visit(module)
    need(visited == set(modules), "Unused or missing copied dependency")
    facade = IMPORT.findall((ROOT / "GenericMT.lean").read_text())
    need(facade == roots, "Import facade differs from selected roots")
    need((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0",
         "Wrong Lean toolchain")
    lake_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = [p for p in lake_manifest["packages"] if p["name"] == "mathlib"]
    need(len(mathlib) == 1 and mathlib[0]["rev"] == MATHLIB_REVISION,
         "Wrong Mathlib revision")
    if source is not None:
        source = source.resolve()
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=source, text=True
        ).strip()
        need(revision == SOURCE_COMMIT, "Comparison checkout is at another revision")
        for row in rows:
            need((source / row["path"]).read_bytes() ==
                 (ROOT / row["path"]).read_bytes(),
                 "Original/copy mismatch: " + row["path"])
    return {
        "status": "PASS", "source_commit": SOURCE_COMMIT,
        "original_MT_modules": 44, "copied_import_closure_modules": 63,
        "original_checkout_compared": source is not None,
        "scope": "Source identities and complete local import closure; not a kernel replay",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="optional original ppg-lean checkout")
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.source), indent=2))
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(json.dumps({"status": "FAIL", "reason": str(error)}))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
