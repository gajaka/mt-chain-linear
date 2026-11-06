#!/usr/bin/env python3
"""Read-only source identity and complete mathematical-module inventory check."""

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
FIXTURES = {
    "artifacts/luces/local_plan.json",
    "artifacts/luces/local_plan_kernel_inputs.json",
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
    need(manifest["schema_version"] == 2, "Unknown source manifest schema")
    need(manifest["source_project"] == "ppg-lean", "Wrong source project")
    need(manifest["source_commit"] == SOURCE_COMMIT, "Wrong source revision")
    rows = manifest["files"]
    need(len(rows) == manifest["source_modules"] == 208, "Wrong module count")
    modules = {}
    paths = set()
    for row in rows:
        module = row["module"]
        path = "/".join(module.split(".")) + ".lean"
        need((module == "PPGraph" or module.startswith("PPGraph.")) and
             row["path"] == path, "Unexpected source module path")
        need(module not in modules and path not in paths, "Duplicate source")
        file = ROOT / path
        need(not file.is_symlink() and file.is_file(), "Missing source module")
        need(file.stat().st_size == row["bytes"] and digest(file) == row["sha256"],
             "Source changed: " + path)
        modules[module] = file
        paths.add(path)
    actual = {p.relative_to(ROOT).as_posix()
              for p in (ROOT / "PPGraph").rglob("*.lean")}
    if (ROOT / "PPGraph.lean").is_file():
        actual.add("PPGraph.lean")
    need(actual == paths, "Missing or extra PPGraph source files")
    for prefix, field, expected in (
        ("PPGraph.MoserTardos.", "moser_tardos_modules", 44),
        ("PPGraph.HLS.", "hls_modules", 63),
        ("PPGraph.Shearer.", "shearer_modules", 16),
    ):
        need(sum(m.startswith(prefix) for m in modules) == manifest[field] == expected,
             "Wrong module inventory: " + prefix)
    roots = manifest["roots"]
    need(roots == ["PPGraph", "PPGraph.All"], "Unexpected entry points")
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
    need(visited == set(modules), "Complete entry points omit a source module")
    facade = IMPORT.findall((ROOT / "GenericMT.lean").read_text())
    need(facade == roots, "Import facade differs from complete entry points")
    fixtures = manifest["elaboration_inputs"]
    need(len(fixtures) == len(FIXTURES) and
         {row["path"] for row in fixtures} == FIXTURES,
         "Missing or extra elaboration input")
    for row in fixtures:
        file = ROOT / row["path"]
        need(not file.is_symlink() and file.is_file(), "Missing elaboration input")
        need(file.stat().st_size == row["bytes"] and digest(file) == row["sha256"],
             "Changed elaboration input: " + row["path"])
        need(isinstance(json.loads(file.read_text()), dict), "Invalid JSON input")
    actual_fixtures = {p.relative_to(ROOT).as_posix()
                       for p in (ROOT / "artifacts").rglob("*") if p.is_file()}
    need(actual_fixtures == FIXTURES, "Unexpected artifact inventory")
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
        tracked = subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=source, text=True
        ).split("\0")
        expected_sources = {p for p in tracked if p.endswith(".lean") and
                            (p == "PPGraph.lean" or p.startswith("PPGraph/"))}
        need(expected_sources == paths, "Incomplete original source inventory")
        for row in rows + fixtures:
            need((source / row["path"]).read_bytes() ==
                 (ROOT / row["path"]).read_bytes(),
                 "Original/source mismatch: " + row["path"])
    return {
        "status": "PASS", "source_commit": SOURCE_COMMIT,
        "mathematical_modules": 208, "implementation_modules": 206,
        "original_MT_modules": 44, "HLS_modules": 63, "Shearer_modules": 16,
        "elaboration_inputs": 2, "original_checkout_compared": source is not None,
        "scope": "Source identities and complete mathematical inventory; not a kernel replay",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="optional source checkout")
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.source), indent=2))
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(json.dumps({"status": "FAIL", "reason": str(error)}))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
