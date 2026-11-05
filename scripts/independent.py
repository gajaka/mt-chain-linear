#!/usr/bin/env python3
"""Fresh raw-process proof export and strict independent Nanoda checking.

All writes stay in this project. The old project is provenance only and is
neither imported nor executed. The --verify mode reads existing evidence only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from export_check import inspect_export
from provenance import validate_sources

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}
SHORT_NAMES = (
    "expected_steps_ge_linear_refined", "expected_steps_ge_linear",
    "expected_steps_le_linear", "linear_work_bounds", "expected_steps_isTheta_linear",
    "expected_steps_not_quadratic_lower", "expected_steps_not_isTheta_quadratic",
    "no_positive_quadratic_lower_bound", "expected_invalidations_le_linear",
)
NAMES = tuple("MTChainFormal.Tightness." + name for name in SHORT_NAMES)
SIDECARS = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".ilean")
FORBIDDEN = ("PPGraph", "PPG", "PPChain", "Profile", "PublicKernelBridge")
MARKER = "THETA_INDEPENDENT_AUDIT "
PINNED_TOOLS = {
    "lean": "d1d9c26a539f54fe839d2aa7760bf1ac1dd76a30b26e2c9684bebf2900038fcf",
    "leanexport": "01327b83d6a69dbc84fa04fd671c61068b2f074e51d1bf607bf6a6b9aed5339e",
    "nanoda": "4f2264a0c987e94c4a654768a90ddb92369014578ecafba3287020bec0f4d439",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def bind(path):
    path = Path(path).absolute()
    return {"path": str(path), "resolved": str(path.resolve()),
            "sha256": sha(path), "bytes": path.stat().st_size}


def verify_bindings(bindings):
    for expected in bindings:
        require(bind(expected["path"]) == expected, "Changed input: " + expected["path"])


def local_inputs():
    provenance = validate_sources(ROOT)
    closure = provenance["closure"]
    require(len(closure) == 30, "Expected exactly thirty raw MT closure modules")
    packages = read(ROOT / "lake-manifest.json")["packages"]
    require(len(packages) == 9, "Unexpected dependency package inventory")
    require(not any(str(p["name"]).startswith(FORBIDDEN) for p in packages),
            "PPGraph/profile package dependency is forbidden")
    libs = [ROOT / ".lake/build/lib/lean"]
    for package in packages:
        package_root = ROOT / ".lake/packages" / package["name"]
        require(package_root.is_dir() and
                package_root.resolve().is_relative_to(ROOT / ".lake/packages"),
                "Dependency resolves outside independent copies: " + str(package_root))
        lib = package_root / ".lake/build/lib/lean"
        # A Lake tool-only dependency can have no loaded Lean artifacts.
        # Actual imports are all required and checked by import_inventory.
        if lib.is_dir():
            require(lib.resolve().is_relative_to(ROOT / ".lake/packages"),
                    "Dependency cache resolves outside independent copies: " + str(lib))
            libs.append(lib)
    required = closure | {"TightnessResults"}
    for module in required:
        path = libs[0] / (module + ".olean")
        require(path.is_file() and path.resolve().is_relative_to(libs[0]),
                "Fresh local module is absent or resolves outside new cache: " + module)
    inputs = [ROOT / x for x in ("SOURCE_MANIFEST.json", "MODULE_MIGRATION.json", "lake-manifest.json",
              "lakefile.lean", "lean-toolchain", "scripts/independent.py",
              "scripts/export_check.py", "scripts/provenance.py", "scripts/verify.py",
              "formal/theta-audit/ADAPTATION.json")]
    inputs = sorted(set(inputs + provenance["all_paths"]))
    return closure, libs, [bind(path) for path in inputs]


def tool_paths(args):
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    require(toolchain == "leanprover/lean4:v4.35.0", "Unexpected Lean toolchain")
    default = Path.home() / ".elan/toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin/lean"
    lean = Path(args.lean or default).resolve()
    exporter = Path(args.leanexport or lean.with_name("leanexport")).resolve()
    nanoda_arg = args.nanoda or os.environ.get("NANODA_BIN") or shutil.which("nanoda_bin")
    require(nanoda_arg is not None, "Pass --nanoda PATH or set NANODA_BIN")
    paths = {"lean": lean, "leanexport": exporter, "nanoda": Path(nanoda_arg).resolve()}
    for name, path in paths.items():
        require(path.is_file() and sha(path) == PINNED_TOOLS[name],
                "Tool differs from pinned checked binary: " + name)
    return paths, {name: bind(path) for name, path in paths.items()}


def primitive_names(lean):
    source = lean.parent.parent / "src/lean/lake/Lake/CLI/Check.lean"
    text = source.read_text()
    body = text.split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0]
    names = re.findall(r"(?m)^\s*``([A-Za-z0-9_.]+),?\s*$", body)
    require(len(names) == 26, "Pinned comparator primitive inventory changed")
    return names + ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"], source


def launch(command, cwd, env, directory, name, timeout, stdout=None):
    log = directory / (name + ".log")
    request = {"command": list(map(str, command)), "cwd": str(cwd),
               "LEAN_PATH": env.get("LEAN_PATH"), "LEAN_SRC_PATH": env.get("LEAN_SRC_PATH"),
               "timeout_seconds": timeout, "parent_stack_limits": list(resource.getrlimit(resource.RLIMIT_STACK))}
    write(directory / (name + "-REQUEST.json"), request)
    started = time.monotonic()
    with log.open("wb") as errors:
        output = stdout.open("wb") if stdout else None
        try:
            process = subprocess.Popen(request["command"], cwd=cwd, env=env,
                stdout=output if output else errors, stderr=errors)
            expired = False
            try:
                process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                expired = True
                process.kill()
                process.wait()
        finally:
            if output:
                output.close()
    result = dict(request, exit_code=process.returncode, timeout=expired,
                  seconds=time.monotonic() - started, log=bind(log),
                  stdout=bind(stdout) if stdout else None,
                  inherited_stack_no_preexec_change=True)
    write(directory / (name + "-PROCESS.json"), result)
    require(process.returncode == 0 and not expired, "Failed " + name + "; inspect " + str(log))
    return result


def import_inventory(audit, closure, lean):
    modules, artifacts = [], {}
    own_lib = ROOT / ".lake/build/lib/lean"
    own_sources = {path.stem for path in (ROOT / "formal").rglob("*.lean")}
    sysroot = lean.parent.parent / "lib/lean"
    seen = set()
    for row in audit["import_inventory"]:
        name = row["module"]
        require(name not in seen, "Duplicate imported module: " + name)
        seen.add(name)
        require(not name.startswith(FORBIDDEN), "Forbidden graph/profile import: " + name)
        path = Path(row["olean"])
        resolved = path.resolve()
        if name in own_sources:
            require(resolved.is_relative_to(own_lib), "Local import resolves outside new build cache: " + name)
        else:
            require(resolved.is_relative_to(ROOT / ".lake/packages") or resolved.is_relative_to(sysroot),
                    "Import resolves outside independent dependencies/toolchain: " + name)
        present = []
        for suffix in SIDECARS:
            sidecar = Path(str(path)[:-len(".olean")] + suffix)
            if sidecar.is_file():
                require(sidecar.resolve().is_relative_to(ROOT) or sidecar.resolve().is_relative_to(sysroot),
                        "Sidecar escapes independent project/toolchain: " + str(sidecar))
                present.append(suffix)
                artifacts[str(sidecar)] = bind(sidecar)
        require(".olean" in present, "Missing imported olean: " + name)
        modules.append(dict(row, present_sidecars=present))
    require(closure | {"TightnessResults"} <= seen, "Required raw MT/facade import is missing")
    return {"module_count": len(modules), "artifact_count": len(artifacts),
            "bytes": sum(row["bytes"] for row in artifacts.values()),
            "modules": modules, "artifacts": list(artifacts.values()),
            "required_raw_modules": sorted(closure), "PPGraph_imports": [],
            "local_imports_resolve_under_new_build": True}


def verify_inventory(inventory):
    verify_bindings(inventory["artifacts"])
    for row in inventory["modules"]:
        stem = row["olean"][:-len(".olean")]
        require([s for s in SIDECARS if Path(stem + s).is_file()] == row["present_sidecars"],
                "Imported sidecar presence changed: " + row["module"])


def check_kernel_log(path, expected):
    matches = re.findall(r"(?m)^Checked ([1-9][0-9]*) declarations with no errors\s*$", path.read_text())
    require(len(matches) == 1 and int(matches[0]) == expected,
            "Nanoda success marker/count mismatch")


def run(args):
    require(re.fullmatch(r"attempt-[0-9]{3,}", args.attempt) is not None, "Invalid attempt name")
    directory = ROOT / "evidence" / args.attempt
    export_dir = ROOT / "evidence/exports" / args.attempt
    require(not directory.exists() and not export_dir.exists(), "Refusing to overwrite prior evidence")
    directory.mkdir(parents=True)
    export_dir.mkdir(parents=True)
    started = time.monotonic()
    result = {"status": "RUNNING", "roots": list(NAMES)}
    stack = resource.getrlimit(resource.RLIMIT_STACK)
    try:
        closure, libs, inputs = local_inputs()
        tools, tool_bindings = tool_paths(args)
        primitives, primitive_source = primitive_names(tools["lean"])
        inputs.append(bind(primitive_source))
        src = directory / "src"; src.mkdir()
        auditor = src / "ThetaIndependentAudit.lean"
        shutil.copyfile(ROOT / "formal/theta-audit/ThetaIndependentAudit.lean", auditor)
        inputs.append(bind(auditor))
        lib = directory / "lib/lean"; lib.mkdir(parents=True)
        env = os.environ.copy()
        for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
            env.pop(key, None)
        env["LEAN_PATH"] = os.pathsep.join(map(str, [lib, *libs]))
        write(directory / "INPUTS.json", {"local_inputs": inputs, "tools": tool_bindings,
            "required_raw_modules": sorted(closure), "LEAN_PATH": env["LEAN_PATH"],
            "LEAN_SRC_PATH": None, "roots": list(NAMES), "allowed_axioms": sorted(ALLOWED),
            "parent_stack_limits": list(stack), "old_projects_executed_or_written": False})
        # Module-mode quotation plus a full-private proof environment coexist.
        # The resource cap changes, not the allowed axioms or checked roots.
        audit_run = launch([tools["lean"], "-j1", "-M8192", "-o",
            lib / "ThetaIndependentAudit.olean", auditor.name], src, env, directory, "audit", args.timeout)
        logs = [line.split(MARKER, 1)[1] for line in Path(audit_run["log"]["path"]).read_text().splitlines() if MARKER in line]
        require(len(logs) == 1, "Expected exactly one raw theorem audit marker")
        audit = json.loads(logs[0]); write(directory / "audit.json", audit)
        require(set(audit["root_names"]) == set(NAMES) and audit["root_count"] == 9,
                "Auditor root inventory differs")
        require(set(audit["raw_kernel_closure_axioms"]) <= ALLOWED, "Forbidden raw closure axiom")
        for row in audit["declarations"]:
            require(row["kind"] == "theorem" and row["has_actual_proof_body"] and row["exact_type_defeq"],
                    "Actual theorem/type/body check failed")
            require(set(row["axioms"]) <= ALLOWED and row["binder_gate"]["status"] == "PASS",
                    "Root axiom/binder check failed")
        inventory = import_inventory(audit, closure, tools["lean"])
        write(directory / "import-inventory.json", inventory)
        result.update(audit=bind(directory / "audit.json"), audit_run=audit_run,
                      inventory=bind(directory / "import-inventory.json"))
        write(directory / "PROGRESS.json", result)
        exported = export_dir / "declarations.ndjson"
        roots = list(dict.fromkeys([*NAMES, *sorted(ALLOWED), *primitives]))
        export_run = launch([tools["leanexport"], "TightnessResults", "--", *roots],
            ROOT, env, directory, "export", args.timeout, exported)
        inspected = inspect_export(exported, NAMES)
        write(directory / "export-inspection.json", inspected)
        config = {"export_file_path": str(exported), "use_stdin": False,
            "permitted_axioms": sorted(ALLOWED), "unpermitted_axiom_hard_error": True,
            "unsafe_permit_all_axioms": False, "num_threads": 1, "nat_extension": True,
            "string_extension": True, "print_success_message": True, "print_axioms": True,
            "pp_to_stdout": True, "pp_declars": list(NAMES), "unknown_pp_declar_hard_error": True}
        config_path = directory / "nanoda.json"; write(config_path, config)
        result.update(export_run=export_run, export_inspection=bind(directory / "export-inspection.json"))
        write(directory / "PROGRESS.json", result)
        kernel = launch([tools["nanoda"], config_path], directory, env, directory, "nanoda", args.timeout)
        check_kernel_log(Path(kernel["log"]["path"]), inspected["expanded_declaration_count"])
        verify_inventory(inventory)
        verify_bindings(inputs + list(tool_bindings.values()))
        require(resource.getrlimit(resource.RLIMIT_STACK) == stack, "Parent stack limits changed")
        result.update(status="PASS", root_count=9, nanoda=kernel,
            checked_declarations=inspected["expanded_declaration_count"], export=bind(exported),
            nanoda_config=bind(config_path), inputs=bind(directory / "INPUTS.json"),
            audit_object=bind(lib / "ThetaIndependentAudit.olean"), seconds=time.monotonic() - started,
            PPGraph_imports=[], standalone_raw_module_count=30,
            imported_modules=inventory["module_count"], inherited_stack_unchanged=True,
            scope="Nine raw-process theorem roots and their exported proof closure, not every assertion in thirty modules; no Python/PRNG/compiler-time or novelty claim.")
        write(directory / "RESULT.json", result)
        return result
    except Exception as error:
        result.update(status="FAIL", error={"type": type(error).__name__, "message": str(error)},
                      seconds=time.monotonic() - started)
        write(directory / "FAILED.json", result)
        raise


def verify(args):
    directory = ROOT / "evidence" / args.attempt
    result = read(directory / "RESULT.json")
    require(result["status"] == "PASS" and result["root_count"] == 9, "No passing raw audit")
    require(tuple(result["roots"]) == NAMES and result["PPGraph_imports"] == [], "Wrong audit scope")
    records = [result[key] for key in ("inputs", "audit", "inventory", "export_inspection",
                                      "export", "nanoda_config", "audit_object")]
    for process in (result["audit_run"], result["export_run"], result["nanoda"]):
        require(process["exit_code"] == 0 and not process["timeout"], "A recorded process failed")
        records.append(process["log"])
        if process["stdout"]:
            records.append(process["stdout"])
    verify_bindings(records)
    inputs = read(result["inputs"]["path"])
    verify_bindings(inputs["local_inputs"] + list(inputs["tools"].values()))
    verify_inventory(read(result["inventory"]["path"]))
    config = read(result["nanoda_config"]["path"])
    require(set(config["permitted_axioms"]) == ALLOWED and config["num_threads"] == 1 and
            not config["unsafe_permit_all_axioms"] and config["unpermitted_axiom_hard_error"] and
            config["unknown_pp_declar_hard_error"] and tuple(config["pp_declars"]) == NAMES,
            "Strict Nanoda configuration changed")
    inspected = inspect_export(Path(result["export"]["path"]), NAMES)
    require(inspected == read(result["export_inspection"]["path"]), "Export inspection changed")
    check_kernel_log(Path(result["nanoda"]["log"]["path"]), inspected["expanded_declaration_count"])
    return {"status": "PASS", "mode": "saved-evidence-read-only", "root_count": 9,
            "checked_declarations": result["checked_declarations"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", default="attempt-001")
    parser.add_argument("--nanoda", type=Path)
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--leanexport", type=Path)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    result = verify(args) if args.verify else run(args)
    print(json.dumps({key: result[key] for key in ("status", "root_count", "checked_declarations")}, indent=2))


if __name__ == "__main__":
    main()
