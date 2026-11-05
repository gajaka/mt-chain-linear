#!/usr/bin/env python3
"""Read-only verification of the original PPGraph snapshot and import closure."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from provenance import lean_imports


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(compare_source=None):
    manifest = json.loads((ROOT / "framework/SOURCE_MANIFEST.json").read_text())
    vendor = ROOT / "vendor/ppg-lean"
    require(not (ROOT / "vendor").is_symlink() and not vendor.is_symlink(), "Snapshot root is a symlink")
    rows = manifest["files"]
    names = [row["path"] for row in rows]
    require(len(names) == len(set(names)), "Duplicate snapshot path")
    for row in rows:
        rel = Path(row["path"])
        require(not rel.is_absolute() and ".." not in rel.parts, "Escaping path")
        path = vendor / rel
        cursor = vendor
        for part in rel.parts:
            cursor /= part
            require(not cursor.is_symlink(), "Symlink in snapshot path: " + str(cursor))
        require(path.is_file() and not path.is_symlink(), "Missing original: " + str(rel))
        require(sha(path) == row["sha256"] and path.stat().st_size == row["bytes"],
                "Snapshot changed: " + str(rel))
        if compare_source:
            require(sha(Path(compare_source) / rel) == row["sha256"],
                    "Source differs: " + str(rel))
    modules = {".".join(Path(p).with_suffix("").parts): vendor / p
               for p in names if p.endswith(".lean") and p != "lakefile.lean"}
    discovered = {".".join(p.relative_to(vendor).with_suffix("").parts)
                  for p in (vendor / "PPGraph").rglob("*.lean")} | {"PPGraph"}
    require(set(modules) == discovered, "Unmanifested or missing library module")
    edges = {name: lean_imports(path.read_text()) for name, path in modules.items()}
    for name, targets in edges.items():
        for target in targets:
            require(target in modules or target.split(".")[0] in {"Lean", "Mathlib", "Std", "Init"},
                    "Unresolved import: " + name + " -> " + target)
    closure = set()
    def visit(name):
        if name not in closure:
            closure.add(name)
            for target in edges[name]:
                if target in modules:
                    visit(target)
    visit("PPGraph.All")
    require(closure == set(modules) - {"PPGraph"}, "All does not cover full original library")
    categories = {
        "MT": "PPGraph.MoserTardos.",
        "MT_probability": "PPGraph.MoserTardos.Probability.",
        "repair_hazard_observable": "PPGraph.Repair.",
        "finite_probability_and_drift": "PPGraph.Finite.",
        "HLS_probability": "PPGraph.HLS.Probability.",
    }
    counts = {key: sum(name.startswith(prefix) for name in modules)
              for key, prefix in categories.items()}
    require(all(counts.values()), "Requested formal layer missing")
    # Build-time literal file inputs: source is byte-identical, but still check
    # that each referenced input is present inside the copied package.
    spec = importlib.util.spec_from_file_location("original_ppgraph_audit", vendor / "tools/audit_ppgraph.py")
    original_audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(original_audit)
    embedded = set()
    for targets in original_audit.included_inputs(modules.values(), vendor).values():
        for target in targets:
            rel = target.relative_to(vendor.resolve()).as_posix()
            require(rel in names, "Unmanifested embedded input: " + rel)
            embedded.add(rel)
    root_lock = json.loads((ROOT / "lake-manifest.json").read_text())
    source_lock = json.loads((vendor / "lake-manifest.json").read_text())
    revisions = lambda lock: {p["name"]: p["rev"] for p in lock["packages"]}
    require(revisions(root_lock) == revisions(source_lock), "Dependency revision mismatch")
    require((ROOT / "lean-toolchain").read_bytes() == (vendor / "lean-toolchain").read_bytes(),
            "Lean version mismatch")
    return {"status": "PASS", "source_commit": manifest["source_commit"],
            "files": len(rows), "proof_modules": len(modules),
            "full_import_closure": len(closure), "categories": counts,
            "embedded_inputs": sorted(embedded),
            "compared_original": str(compare_source) if compare_source else None,
            "source_manifest_sha256": sha(ROOT / "framework/SOURCE_MANIFEST.json"),
            "scope": "Source identity/import/dependency checks; not a Lean or Nanoda run"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-source", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify(args.compare_source)
    if args.output:
        with args.output.open("x") as handle:
            json.dump(result, handle, indent=2)
            handle.write("\n")
    print(json.dumps(result, indent=2))
