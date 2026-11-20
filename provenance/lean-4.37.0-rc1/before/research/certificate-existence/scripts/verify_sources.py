#!/usr/bin/env python3
"""Read-only validation of the certificate study and its standalone core.

An optional --output writes a new receipt, never replaces an existing one.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT.parents[1]
_spec = importlib.util.spec_from_file_location("mt_core_provenance", CORE / "scripts/provenance.py")
_core_provenance = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_core_provenance)
validate_core = _core_provenance.validate_sources
lean_imports = _core_provenance.lean_imports


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_sources(compare_original=False):
    core = validate_core(CORE)
    paths = set(core["all_paths"])

    def local(relative):
        p = Path(relative)
        need(not p.is_absolute() and ".." not in p.parts, "Escaping study path")
        p = ROOT / p
        need(p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT),
             "Absent or external study source: " + relative)
        paths.add(p)
        return p

    manifest = json.loads(local("SOURCE_MANIFEST.json").read_text())
    need(manifest["schema_version"] == 2, "Expected complete study manifest")
    adaptations = json.loads(local("COPY_ADAPTATIONS.json").read_text())
    copied = manifest["copied_separation_modules"]
    need(len(copied) == 14, "Expected fourteen copied separation modules")
    cleanup = {r["path"]: r for r in adaptations["copy_inventory"]}
    need(len(cleanup) == 14, "Duplicate/missing cleanup inventory")
    recorded = set()
    for row in copied:
        name = row["active"]
        need(name not in recorded, "Duplicate copied source")
        recorded.add(name)
        before = local(row["archive"])
        after = local(name)
        need(sha(before) == row["original_sha256"] == cleanup[name]["original_sha256"],
             "Changed archived source: " + name)
        lines = before.read_bytes().splitlines(keepends=True)
        k = 0
        while lines[k].startswith(b"import "):
            k += 1
        header_version = (b"module\n\n" + b"".join(b"public " + x for x in lines[:k]) +
                          b"\n@[expose] public section\n" + b"".join(lines[k:]))
        need(hashlib.sha256(header_version).hexdigest() == cleanup[name]["after_module_header_sha256"],
             "Wrong header migration: " + name)
        need(sha(after) == row["active_sha256"] == cleanup[name]["current_sha256"],
             "Changed migrated source: " + name)
        if not cleanup[name]["has_post_header_cleanup"]:
            need(after.read_bytes() == header_version, "Unrecorded copied-source edit")
        need(set(lean_imports(before.read_text())) == set(lean_imports(after.read_text())),
             "Changed copied-module import set")
        if compare_original:
            need(sha(Path(row["source"])) == row["original_sha256"], "Original project changed")
    new = manifest["new_mathematical_sources"]
    need({r["path"] for r in new} == {
        "formal/CertificateConstruction.lean", "formal/ExponentialObstruction.lean",
        "formal/NeighborEmbedding.lean", "formal/CertificateResults.lean"},
        "Unexpected new mathematical sources")
    for row in new:
        need(row["path"] not in recorded, "Overlapping source inventories")
        recorded.add(row["path"])
        need(sha(local(row["path"])) == row["sha256"], "Changed new proof source")
    actual = {str(p.relative_to(ROOT)) for p in (ROOT / "formal").glob("*.lean")}
    need(actual == recorded and len(actual) == 18, "Missing/unmanifested mathematical source")
    modules = {Path(name).stem: local(name) for name in recorded}
    need(len(modules) == 18, "Duplicate module basename")
    all_modules = dict(core["modules"])
    need(not set(all_modules) & set(modules), "Core/study module collision")
    all_modules.update(modules)
    dependencies = {}
    for name, p in all_modules.items():
        imports = lean_imports(p.read_text())
        for target in imports:
            need(target in all_modules or target.split(".")[0] in {"Mathlib", "Lean", "Init", "Std"},
                 "Unexpected import: " + target)
        dependencies[name] = [x for x in imports if x in all_modules]
    closure = set()

    def visit(name):
        if name not in closure:
            closure.add(name)
            for target in dependencies[name]:
                visit(target)

    visit("CertificateResults")
    need(set(modules) <= closure, "Study module absent from final result closure")
    support = manifest["audit_tooling_and_support"]
    seen = set()
    for row in support:
        need(row["path"] not in seen, "Duplicate support binding")
        seen.add(row["path"])
        need(sha(local(row["path"])) == row["sha256"], "Changed audit/tooling/support input")
    required = {str(p.relative_to(ROOT)) for d in ["audit", "scripts"]
                for p in (ROOT / d).rglob("*") if p.is_file() and p.suffix in {".lean", ".py"}}
    required |= {"lakefile.lean", "lake-manifest.json", "lean-toolchain", "COPY_ADAPTATIONS.json"}
    need(required <= seen, "Unbound audit/tooling/build input")
    lock = json.loads(local("lake-manifest.json").read_text())
    packages = lock["packages"]
    root_package = [p for p in packages if p["name"] == "mtChainLinear"]
    need(len(root_package) == 1 and root_package[0]["type"] == "path" and
         root_package[0]["dir"] == "../..", "Wrong standalone core dependency")
    old_packages = json.loads((CORE / "lake-manifest.json").read_text())["packages"]
    need({p["name"]: p.get("rev") for p in packages if p["name"] != "mtChainLinear"} ==
         {p["name"]: p["rev"] for p in old_packages} and len(packages) == 10,
         "Changed pinned dependency set")
    need(local("lean-toolchain").read_bytes() == (CORE / "lean-toolchain").read_bytes(),
         "Wrong research toolchain")
    return {"paths": sorted(paths), "receipt": {
        "status": "PASS", "copied_separation_modules": 14, "new_mathematical_modules": 4,
        "final_local_import_closure": sorted(closure), "closure_module_count": len(closure),
        "PPGraph_imports": [], "source_manifest_sha256": sha(ROOT / "SOURCE_MANIFEST.json"),
        "core_source_validation": core["receipt"],
        "original_separation_sources_compared": 14 if compare_original else 0,
        "scope": "Source/provenance/import validation; not a new kernel replay"}}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--compare-original", action="store_true")
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    receipt = validate_sources(args.compare_original)["receipt"]
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as f:
            json.dump(receipt, f, indent=2)
            f.write("\n")
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
