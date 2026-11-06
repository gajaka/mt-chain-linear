#!/usr/bin/env python3
"""Read-only source identity and exact MT-theory dependency-closure check."""

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
FAMILIES = {
    "PPGraph.MoserTardos.": ("moser_tardos_modules", 44),
    "PPGraph.HLS.": ("hls_modules", 63),
    "PPGraph.Shearer.": ("shearer_modules", 16),
    "PPGraph.LLL.": ("lll_modules", 3),
}
REPAIR_ROOTS = {
    "PPGraph.Repair.Hazards", "PPGraph.Repair.SemanticHazards",
    "PPGraph.Repair.ObservableAlgebra", "PPGraph.Repair.ObservableKernel",
}
POLICY_ROOTS = {
    "PPGraph.Integration.Policy.History",
    "PPGraph.Integration.Policy.MoserTardos",
    "PPGraph.Integration.Policy.HLSCounting",
    "PPGraph.Integration.Policy.HLSDAG",
    "PPGraph.Integration.Policy.HLSExpectation",
}
FORBIDDEN = (
    "PPGraph.Decision.", "PPGraph.Certification.",
    "PPGraph.Optimization.",
)
IMPORT = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+"
    r"([A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(module):
    return module.replace(".", "/") + ".lean"


def selected_roots(modules):
    return {m for m in modules if any(m.startswith(p) for p in FAMILIES)} | REPAIR_ROOTS | POLICY_ROOTS


def check(source=None):
    manifest = json.loads((ROOT / "SOURCES.json").read_text())
    need(manifest["schema_version"] == 3, "Unknown source manifest schema")
    need(manifest["source_project"] == "ppg-lean", "Wrong source project")
    need(manifest["source_commit"] == SOURCE_COMMIT, "Wrong source revision")
    rows = manifest["files"]
    need(len(rows) == manifest["source_modules"] == 150, "Wrong source count")
    modules = {}
    paths = set()
    for row in rows:
        module = row["module"]
        path = module_path(module)
        need(module.startswith("PPGraph.") and row["path"] == path,
             "Unexpected source module path")
        need(module != "PPGraph.All" and not module.startswith(FORBIDDEN),
             "Unrelated module: " + module)
        need(module not in modules and path not in paths, "Duplicate source")
        file = ROOT / path
        need(not file.is_symlink() and file.is_file(), "Missing source module")
        need(file.stat().st_size == row["bytes"] and digest(file) == row["sha256"],
             "Source changed: " + path)
        modules[module] = file
        paths.add(path)
    actual = {p.relative_to(ROOT).as_posix()
              for p in (ROOT / "PPGraph").rglob("*.lean")}
    if (ROOT / "PPGraph.lean").exists():
        actual.add("PPGraph.lean")
    need(actual == paths, "Missing or extra mathematical source")
    for prefix, (field, count) in FAMILIES.items():
        need(sum(m.startswith(prefix) for m in modules) == manifest[field] == count,
             "Wrong requested-family inventory: " + prefix)
    need(set(manifest["repair_roots"]) == REPAIR_ROOTS and
         set(manifest["policy_roots"]) == POLICY_ROOTS,
         "Wrong hazard, observable or policy scope")
    roots = manifest["roots"]
    expected_roots = selected_roots(modules)
    need(len(roots) == len(set(roots)) == manifest["requested_root_modules"] == 135
         and set(roots) == expected_roots, "Wrong requested root set")
    visited = set()

    def visit(module):
        if module in visited:
            return
        need(module in modules, "Missing dependency: " + module)
        visited.add(module)
        for imported in IMPORT.findall(modules[module].read_text()):
            if imported.startswith("PPGraph"):
                visit(imported)
            else:
                need(imported.split(".")[0] in {"Mathlib", "Lean", "Std", "Init"},
                     "Unexpected external dependency: " + imported)

    for module in roots:
        visit(module)
    need(visited == set(modules), "Unused or missing dependency module")
    support = sorted(set(modules) - expected_roots)
    need(support == manifest["dependency_only"] and
         len(support) == manifest["dependency_modules"] == 15,
         "Wrong dependency-only inventory")
    for row in rows:
        role = "requested_root" if row["module"] in expected_roots else "dependency"
        need(row["role"] == role, "Wrong source role")
    need(IMPORT.findall((ROOT / "GenericMT.lean").read_text()) == roots,
         "Entry point differs from the requested root set")
    config = (ROOT / "lakefile.lean").read_text()
    root_block = re.search(r'lean_lib PPGraph where.*?roots := #\[(.*?)\]',
                           config, re.DOTALL)
    need(root_block is not None and
         re.findall(r'`([A-Za-z_][A-Za-z0-9_.]*)', root_block.group(1)) == sorted(modules),
         "Lake must register exactly the requested theories and their dependencies")
    need(not re.search(r"\bglobs\s*:=", config), "Broad library globs are not permitted")
    need(manifest["elaboration_inputs"] == [] and not (ROOT / "artifacts").exists(),
         "Unrelated application fixtures are present")
    need((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0",
         "Wrong Lean toolchain")
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    mathlib = [p for p in packages if p["name"] == "mathlib"]
    need(len(mathlib) == 1 and mathlib[0]["rev"] == MATHLIB_REVISION,
         "Wrong Mathlib revision")
    if source is not None:
        source = source.resolve()
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=source, text=True
        ).strip()
        need(revision == SOURCE_COMMIT, "Comparison source is at another revision")
        tracked = subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=source, text=True
        ).split("\0")
        source_modules = {p[:-5].replace("/", ".") for p in tracked
                          if p.endswith(".lean") and p.startswith("PPGraph/")}
        need(selected_roots(source_modules) == expected_roots,
             "Incomplete requested source families")
        for row in rows:
            need((source / row["path"]).read_bytes() ==
                 (ROOT / row["path"]).read_bytes(),
                 "Source identity mismatch: " + row["path"])
    return {
        "status": "PASS", "source_commit": SOURCE_COMMIT,
        "theory_modules": 150, "requested_roots": 135, "dependency_only": 15,
        "MT_modules": 44, "HLS_modules": 63, "Shearer_modules": 16,
        "LLL_modules": 3, "repair_roots": 4, "policy_roots": 5,
        "elaboration_inputs": 0, "source_checkout_compared": source is not None,
        "scope": "Requested theories, exact import closure and source identities; not a kernel replay",
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
