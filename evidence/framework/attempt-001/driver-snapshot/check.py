#!/usr/bin/env python3
"""Build the copied original framework and write fresh, separate audit receipts.

The original audit's pure inspectors and Lean harness bodies are reused without
calling its report-writing main. Historical vendor reports are never rewritten.
This is a Lean build and reported-axiom audit, not a Nanoda/raw-closure replay.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
VENDOR = ROOT / "vendor/ppg-lean"
sys.path.insert(0, str(HERE))
from verify_copy import verify


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    base = ROOT / "evidence/framework"
    base.mkdir(parents=True, exist_ok=True)
    if args.output:
        out = args.output.resolve()
    else:
        n = 1
        while (base / f"attempt-{n:03d}").exists():
            n += 1
        out = base / f"attempt-{n:03d}"
    out.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    result = {"status": "RUNNING", "scope": "Copied original framework: source identity, Lean build, whole-library reported axioms",
              "nanoda_run": False, "crew_instantiation": False, "theta_transfer": False,
              "audit_driver_sha256": sha(Path(__file__))}
    commands = []
    toolchain = (HERE / "lean-toolchain").read_text().strip()
    lake = Path.home() / ".elan/toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin/lake"

    def command(name, argv):
        print(name, flush=True)
        t0 = time.monotonic()
        env = os.environ.copy()
        env.setdefault("LEAN_NUM_THREADS", "4")
        with (out / (name + ".log")).open("w") as log:
            proc = subprocess.run([str(lake), *argv], cwd=HERE, env=env,
                                  stdout=log, stderr=subprocess.STDOUT, check=False)
        commands.append({"name": name, "argv": [str(lake), *argv],
                         "exit_code": proc.returncode, "seconds": time.monotonic() - t0,
                         "log_sha256": sha(out / (name + ".log"))})
        if proc.returncode:
            raise RuntimeError(name + " failed; see " + str(out / (name + ".log")))
        return (out / (name + ".log")).read_text()

    try:
        result["source_before"] = verify()
        # Reuse the root's already pinned dependency checkout when present.
        # This link is generated build state, not a dependency on ppg-lean's
        # checkout or old compiled PPGraph objects.
        packages = HERE / ".lake/packages"
        if not packages.exists() and (ROOT / ".lake/packages").is_dir():
            packages.parent.mkdir(exist_ok=True)
            packages.symlink_to("../../.lake/packages", target_is_directory=True)
        command("build", ["build", "PPGraph", "FrameworkAudit"])
        command("representative-roots", ["env", "lean", "FrameworkAudit.lean"])
        spec = importlib.util.spec_from_file_location("original_audit", VENDOR / "tools/audit_ppgraph.py")
        audit = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(audit)
        canonical, facades = audit.load_module_map(VENDOR)
        audit.validate_lake_configuration(VENDOR)
        audit.inspect_library_sources(canonical, facades)
        modules = sorted({**canonical, **facades})
        owners = audit.included_inputs([*canonical.values(), *facades.values()], VENDOR)
        for n, path in enumerate(sorted(owners)):
            command(f"embedded-input-{n}", ["env", "lean", str(path)])
        # The trusted script supplies inspection commands, not proof axioms.
        # Keep the generated harnesses and their complete output for review.
        for name, body in (("inventory", audit.INVENTORY_BODY), ("axioms", audit.DEPENDENCY_BODY)):
            harness = out / (name + ".lean")
            harness.write_text("\n".join("import " + m for m in modules) + "\n" + body)
            command(name, ["env", "lean", str(harness)])
        inventory = audit.inventory_from_output((out / "inventory.log").read_text(), canonical, facades)
        entries = {e["name"]: {"module": m, **e} for m, es in inventory.items() for e in es}
        dependencies = audit.dependencies_from_output((out / "axioms.log").read_text(), entries)
        explicit = {}
        for module, path in canonical.items():
            declarations, checks = audit.inspect_source(path.read_text(), module)
            names, absent = audit.missing_checks(declarations, checks, inventory[module])
            if absent:
                raise RuntimeError("Original theorem lacks explicit #check: " + str(absent))
            explicit[module] = names
        (out / "DECLARATIONS.json").write_text(json.dumps(
            {name: {**entry, "axioms": dependencies[name]} for name, entry in sorted(entries.items())}, indent=2) + "\n")
        result.update(status="PASS", canonical_modules=len(canonical), facades=len(facades),
                      project_declarations=len(entries), explicit_theorems=sum(map(len, explicit.values())),
                      generated_theorems=sum(e["kind"] == "theorem" for e in entries.values()) - sum(map(len, explicit.values())),
                      allowed_axioms=sorted(audit.ALLOWED), project_owned_axioms=0,
                      source_after=verify(), original_audit_tool_sha256=sha(VENDOR / "tools/audit_ppgraph.py"),
                      declarations_sha256=sha(out / "DECLARATIONS.json"))
    except BaseException as exc:
        result.update(status="FAIL", error=str(exc), traceback=traceback.format_exc())
    finally:
        result.update(commands=commands, seconds=time.monotonic() - started)
        (out / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({k: result[k] for k in ("status", "seconds")}, indent=2), flush=True)
        print(out / "RESULT.json", flush=True)
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
