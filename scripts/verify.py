#!/usr/bin/env python3
"""Verify source identities and the standalone import boundary.

This writes a fresh source-verification receipt; it does not run Lean/Nanoda.
The optional original-project check is read-only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"Mathlib", "Lean", "Std", "Init"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-source", type=Path)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "evidence/source-verification.json")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "SOURCE_MANIFEST.json").read_text())
    copies = manifest["copied_files"]
    need(len(copies) == manifest["copy_count"] == 32, "Wrong copy inventory")
    destinations = set()
    for row in copies:
        path = ROOT / row["destination"]
        need(not path.is_symlink(), "Copied source is a symlink: " + str(path))
        need(path.stat().st_size == row["bytes"], "Wrong source size: " + str(path))
        need(digest(path) == row["sha256_source"] == row["sha256_copy"],
             "Copied source changed: " + str(path))
        destinations.add(row["destination"])
    for row in manifest["adapted_files"]:
        path = ROOT / row["destination"]
        need(digest(path) == row["sha256_adapted"], "Adaptation changed: " + str(path))
        if path.suffix == ".lean":
            destinations.add(row["destination"])
    for row in manifest.get("tooling_files", []):
        need(digest(ROOT / row["destination"]) == row["sha256"],
             "Tooling source changed: " + row["destination"])

    modules = {p.stem: p for p in (ROOT / "formal").rglob("*.lean")}
    need(len(modules) == len(list((ROOT / "formal").rglob("*.lean"))),
         "Duplicate local module basename")
    need({str(p.relative_to(ROOT)) for p in modules.values()} == destinations,
         "Unmanifested or missing Lean sources")
    dependencies = {}
    for name, path in modules.items():
        imports = []
        for line in re.findall(r"^import\s+([^\n]+)", path.read_text(), re.M):
            imports.extend(line.split())
        for target in imports:
            need(target in modules or target.split(".")[0] in STANDARD,
                 "Undeclared import: " + name + " -> " + target)
        dependencies[name] = [target for target in imports if target in modules]

    closure = set()

    def visit(name):
        if name not in closure:
            closure.add(name)
            for target in dependencies[name]:
                visit(target)

    visit("LinearAsymptotics")
    recorded = {Path(row["destination"]).stem for row in copies
                if row["role"] == "theta-import-closure"}
    need(closure == recorded and len(closure) == 30, "Theta closure differs")
    need(not {"Accounting", "Barrier"} & closure, "Paper supplement entered Theta")
    lock = json.loads((ROOT / "lake-manifest.json").read_text())
    need({p["name"] for p in lock["packages"]} == {
        "mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
        "aesop", "Qq", "batteries", "Cli"}, "Unexpected package dependencies")
    mathlib = next(p for p in lock["packages"] if p["name"] == "mathlib")
    need(mathlib["rev"] == "56a005855ea17e0b0958f73ec801ae140b0a1679",
         "Wrong Mathlib revision")
    need((ROOT / "lean-toolchain").read_text().strip() ==
         "leanprover/lean4:v4.35.0", "Wrong Lean toolchain")

    compared = 0
    if args.compare_source:
        source = args.compare_source.resolve()
        for row in manifest["source_project_baseline"]:
            need(digest(source / row["path"]) == row["sha256"],
                 "Original project changed: " + row["path"])
            compared += 1
        for row in copies:
            relative = Path(row["source"]).relative_to(manifest["source_project"])
            need(digest(source / relative) == row["sha256_copy"],
                 "Original/copy differ: " + str(relative))
        for row in manifest["adapted_files"]:
            if "source" in row:
                relative = Path(row["source"]).relative_to(manifest["source_project"])
                need(digest(source / relative) == row["sha256_source"],
                     "Original adaptation source changed: " + str(relative))

    result = {
        "status": "PASS", "exact_copies": len(copies),
        "adapted_files": len(manifest["adapted_files"]),
        "theta_modules": sorted(closure), "theta_module_count": len(closure),
        "public_ppgraph_imports": 0, "ppgraph_package_present": False,
        "source_project_baseline_files_checked": compared,
        "scope": "Source identities/import boundary only; not a kernel proof replay",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
