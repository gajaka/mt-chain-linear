"""Validate historical extraction, exact module migration and active inputs.

The immutable extraction manifest describes archived pre-migration bytes.
MODULE_MIGRATION.json describes the current files. No historical receipt is
rewritten or silently reinterpreted as verification of the migrated sources.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = "provenance/module-migration/before"
AUDIT = "formal/theta-audit/ThetaIndependentAudit.lean"
STANDARD = {"Mathlib", "Lean", "Std", "Init"}
TOOLS = {"scripts/provenance.py", "scripts/verify.py", "scripts/independent.py",
         "scripts/export_check.py"}
SUPPORT = {"lakefile.lean", "lake-manifest.json", "lean-toolchain",
           "formal/theta-audit/ADAPTATION.json"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _sha(value):
    need(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value),
         "Invalid SHA-256 encoding")
    return value


def _relative(value):
    need(isinstance(value, str) and value, "Missing relative path")
    p = PurePosixPath(value)
    need(not p.is_absolute() and str(p) == value and
         not any(part in {".", ".."} for part in p.parts),
         "Noncanonical or escaping path: " + value)
    return p


def _file(root, relative):
    parts = _relative(relative).parts
    path = root.joinpath(*parts)
    cursor = root
    for part in parts:
        cursor = cursor / part
        need(not cursor.is_symlink(), "Symlink in source path: " + str(cursor))
    need(path.is_file() and path.resolve().is_relative_to(root.resolve()),
         "Missing or external input: " + str(path))
    return path


def _rows(rows, field, label):
    need(isinstance(rows, list), "Missing inventory: " + label)
    result = {}
    for row in rows:
        need(isinstance(row, dict), "Invalid inventory row: " + label)
        key = str(_relative(row.get(field)))
        need(key not in result, "Duplicate " + label + ": " + key)
        result[key] = row
    return result


def replay_transform(before, recipe, path):
    """Replay only the fixed proof header edit or an explicit audit-only recipe."""
    kind = recipe if isinstance(recipe, str) else recipe.get("kind") if isinstance(recipe, dict) else None
    if path != AUDIT:
        need(kind == "module-public-section-v1", "Proof body migration is forbidden: " + path)
        match = re.match(rb"\A((?:import[^\r\n]*\n)+)", before)
        need(match is not None, "Expected initial import block: " + path)
        imports = match.group(1)
        public = b"".join(b"public " + line for line in imports.splitlines(keepends=True))
        return b"module\n\n" + public + b"\n@[expose] public section\n" + before[len(imports):]
    need(kind == "exact-replacements-v1" and isinstance(recipe, dict),
         "Audit requires an explicit finite replacement recipe")
    replacements = recipe.get("replacements")
    need(isinstance(replacements, list) and replacements, "Empty audit replacement recipe")
    result = before
    for row in replacements:
        need(isinstance(row, dict) and isinstance(row.get("before"), str) and
             isinstance(row.get("after"), str), "Invalid audit replacement")
        old, new = row["before"].encode("utf-8"), row["after"].encode("utf-8")
        need(old and old != new and result.count(old) == 1,
             "Audit replacement must match exactly once")
        result = result.replace(old, new, 1)
    return result


def _masked(text):
    """Mask comments and quoted strings while preserving positions/newlines."""
    result, i, depth, string = [], 0, 0, False
    while i < len(text):
        c = text[i]
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  "); i += 2; continue
            if pair == "-/":
                depth -= 1
                result.extend("  "); i += 2; continue
            result.append("\n" if c == "\n" else " "); i += 1; continue
        if string:
            if c == "\\" and i + 1 < len(text):
                result.extend("\n" if x == "\n" else " " for x in text[i:i + 2])
                i += 2; continue
            if c == '"': string = False
            result.append("\n" if c == "\n" else " "); i += 1; continue
        if pair == "/-":
            depth = 1
            result.extend("  "); i += 2; continue
        if pair == "--":
            end = text.find("\n", i)
            if end == -1: end = len(text)
            result.extend(" " * (end - i)); i = end; continue
        if c == '"':
            string = True
            result.append(" "); i += 1; continue
        result.append(c); i += 1
    need(depth == 0 and not string, "Unclosed comment or string in Lean source")
    return "".join(result)


def lean_imports(text):
    # Lean 4.35 grammar: [public] [meta] import [all] Module.Name.
    # Newlines may occur between tokens. Comments/strings cannot hide imports.
    masked = _masked(text)
    name = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
    pattern = re.compile(r"(?m)^[ \t]*(?P<public>public\s+)?(?P<meta>meta\s+)?"
                         r"import\s+(?P<all>all\s+)?(?P<name>" + name + r")(?=[ \t]*(?:\n|$))")
    matches = list(pattern.finditer(masked))
    for token in re.finditer(r"\bimport\b", masked):
        need(any(m.start() <= token.start() < m.end() for m in matches),
             "Unsupported import syntax")
    result = []
    for match in matches:
        need(not (match["public"] and match["all"]), "Invalid public import all")
        result.append(match["name"])
    return result


def validate_sources(root=ROOT, compare_source=None):
    """Return manifest/migration, closure/modules, all_paths and receipt.

    all_paths is the complete local source/provenance/tooling input inventory
    for a fresh independent-checker run. This routine does not execute Lean,
    Nanoda or write any receipt. Optional source comparison is read-only.
    """
    root = Path(root).absolute()
    paths = set()

    def local(relative):
        path = _file(root, relative)
        paths.add(path)
        return path

    original_path = local("SOURCE_MANIFEST.json")
    migration_path = local("MODULE_MIGRATION.json")
    manifest = json.loads(original_path.read_text())
    migration = json.loads(migration_path.read_text())
    need(migration.get("schema_version") == 1, "Unsupported migration schema")
    need(migration.get("archived_root") == ARCHIVE, "Unexpected migration archive root")
    need(digest(original_path) == _sha(migration.get("extraction_manifest_sha256")),
         "Extraction manifest substitution or change")
    need(digest(local(ARCHIVE + "/SOURCE_MANIFEST.json")) == digest(original_path),
         "Archived extraction manifest differs")

    copies = _rows(manifest.get("copied_files"), "destination", "extraction copy")
    adapted = _rows(manifest.get("adapted_files"), "destination", "extraction adaptation")
    need(len(copies) == manifest.get("copy_count") == 32, "Wrong extraction copy inventory")
    need(not set(copies) & set(adapted), "Overlapping copy/adaptation inventory")
    expected = {}
    for name, row in copies.items():
        need(row["sha256_source"] == row["sha256_copy"], "Inconsistent extraction copy hash")
        archived = local(ARCHIVE + "/" + name)
        need(digest(archived) == _sha(row["sha256_copy"]) and archived.stat().st_size == row["bytes"],
             "Archived exact extraction copy changed: " + name)
        expected[name] = row["sha256_copy"]
    for name, row in adapted.items():
        need(name.endswith(".lean"), "Unexpected non-Lean extraction adaptation")
        need(digest(local(ARCHIVE + "/" + name)) == _sha(row["sha256_adapted"]),
             "Archived extraction adaptation changed: " + name)
        expected[name] = row["sha256_adapted"]
    need(len(expected) == 34 and AUDIT in expected, "Wrong pre-migration source inventory")
    for name, row in _rows(manifest.get("tooling_files", []), "destination", "old tooling").items():
        need(digest(local(ARCHIVE + "/" + name)) == _sha(row["sha256"]),
             "Archived original tooling changed: " + name)

    source_rows = _rows(migration.get("source_files"), "path", "migrated source")
    need(set(source_rows) == set(expected), "Missing or unmanifested migrated source")
    active_files = {str(p.relative_to(root)) for p in (root / "formal").rglob("*.lean")}
    old_files = {str(p.relative_to(root / ARCHIVE))
                 for p in (root / ARCHIVE / "formal").rglob("*.lean")}
    need(active_files == old_files == set(expected), "Missing, duplicate or unmanifested Lean source")
    modules, dependencies = {}, {}
    for name, row in source_rows.items():
        before = local(ARCHIVE + "/" + name)
        after = local(name)
        need(row["before_sha256"] == expected[name] == digest(before), "Wrong migration origin: " + name)
        need(digest(after) == _sha(row["after_sha256"]), "Active migrated source changed: " + name)
        need(replay_transform(before.read_bytes(), row.get("transform"), name) == after.read_bytes(),
             "Migration changes unrecorded bytes: " + name)
        need(_masked(after.read_text()).lstrip().startswith("module\n"), "Missing module declaration: " + name)
        old_imports, new_imports = lean_imports(before.read_text()), lean_imports(after.read_text())
        need(set(old_imports) == set(new_imports), "Migration changed imported modules: " + name)
        module = after.stem
        need(module not in modules, "Duplicate local module basename: " + module)
        modules[module] = after
        dependencies[module] = new_imports
    for module, targets in dependencies.items():
        for target in targets:
            need(target in modules or target.split(".")[0] in STANDARD,
                 "Undeclared import: " + module + " -> " + target)
        dependencies[module] = [target for target in targets if target in modules]
    closure = set()

    def visit(module):
        if module not in closure:
            closure.add(module)
            for dependency in dependencies[module]: visit(dependency)

    visit("LinearAsymptotics")
    recorded = {Path(name).stem for name, row in copies.items() if row["role"] == "theta-import-closure"}
    need(closure == recorded and len(closure) == 30, "Theta source import closure differs")
    need(not {"Accounting", "Barrier"} & closure, "Supplement entered Theta premises")

    tooling = _rows(migration.get("tooling_files"), "path", "active tooling")
    supporting = _rows(migration.get("supporting_files"), "path", "active support")
    need(TOOLS <= set(tooling), "Missing shared validator or verification tooling binding")
    need(SUPPORT <= set(supporting), "Missing supporting build/audit binding")
    need(not (set(tooling) & set(supporting) or (set(tooling) | set(supporting)) & set(source_rows)),
         "Overlapping migration inventories")
    scripts = {str(p.relative_to(root)) for p in (root / "scripts").rglob("*.py")}
    need(scripts == set(tooling), "Unmanifested or missing active Python tooling")
    for name, row in {**tooling, **supporting}.items():
        need(name != "MODULE_MIGRATION.json", "Self-referential migration hash")
        need(digest(local(name)) == _sha(row["sha256"]), "Active tooling/support changed: " + name)

    lock = json.loads(local("lake-manifest.json").read_text())
    packages = lock["packages"]
    package_names = [p["name"] for p in packages]
    need(len(package_names) == len(set(package_names)) and set(package_names) == {
        "mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
        "aesop", "Qq", "batteries", "Cli"}, "Unexpected package dependencies")
    need(next(p for p in packages if p["name"] == "mathlib")["rev"] ==
         "56a005855ea17e0b0958f73ec801ae140b0a1679", "Wrong Mathlib revision")
    need(local("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0", "Wrong Lean toolchain")

    compared = 0
    if compare_source is not None:
        source = Path(compare_source).absolute()
        baseline = _rows(manifest.get("source_project_baseline"), "path", "original project baseline")
        for name, row in baseline.items():
            need(digest(_file(source, name)) == _sha(row["sha256"]), "Original project changed: " + name)
            compared += 1
        for name, row in {**copies, **adapted}.items():
            relative = str(Path(row["source"]).relative_to(manifest["source_project"]))
            need(digest(_file(source, relative)) == _sha(row["sha256_source"]),
                 "Original source no longer matches archived extraction: " + relative)

    receipt = {
        "status": "PASS", "archived_exact_extraction_copies": len(copies),
        "archived_extraction_adaptations": len(adapted), "active_migrated_Lean_sources": len(source_rows),
        "header_only_proof_migrations": len(source_rows) - 1, "explicit_audit_migrations": 1,
        "theta_modules": sorted(closure), "theta_module_count": len(closure),
        "public_ppgraph_imports": 0, "ppgraph_package_present": False,
        "extraction_manifest_sha256": digest(original_path), "migration_manifest_sha256": digest(migration_path),
        "source_project_baseline_files_checked": compared,
        "scope": "Archived extraction identities and exact active module migration; not a kernel proof replay",
    }
    return {"manifest": manifest, "migration": migration, "closure": closure,
            "modules": modules, "all_paths": sorted(paths), "receipt": receipt}
