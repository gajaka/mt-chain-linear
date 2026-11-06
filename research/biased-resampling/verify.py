#!/usr/bin/env python3
"""Fresh local proof replay. Preserves attempts; updates only RESULT.json.

The mathematical sources are copied verbatim. Only dependency paths in the
copied Lake configuration/manifest are adapted to the current checkout.
Pinned dependency builds may be reused; every study module is rebuilt.
"""

from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


STUDY = Path(__file__).resolve().parent
PROJECT = STUDY.parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MARKER = "BIASED_RESAMPLING_AUDIT "
REQUIRED = {
    "pointwise_drift", "initialWeight_uniform", "initial_static_bad_moment",
    "adaptiveTotalWork_le_potential", "adaptiveTotalWork_le_linear",
    "adaptiveTotalWork_lt_top", "adaptive_biased_initial_upper",
    "adaptive_uniform_initial_upper", "static_linear_work_bounds",
    "expected_steps_isTheta_linear", "policy_space_nonempty",
    "Controls.uniform_unit_drift_fails", "Controls.threshold_only_scaled_drift_fails",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(source: str) -> str:
    """Remove nested Lean comments and string contents before token screening."""
    result = []
    index = 0
    depth = 0
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            index = len(source) if end < 0 else end
        elif source[index] == '"':
            index += 1
            while index < len(source) and source[index] != '"':
                index += 2 if source[index] == "\\" else 1
            index += 1
            result.append(" ")
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


def dump(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def source_inputs() -> list[Path]:
    files = list((STUDY / "formal").glob("*.lean"))
    files += [STUDY / x for x in ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "verify.py")]
    files += [STUDY / x for x in ("README.md", "REPORT.md") if (STUDY / x).exists()]
    files += [PROJECT / x for x in ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "SOURCE_MANIFEST.json")]
    # Resolve the actual local mathematical import closure, excluding Mathlib.
    owners = {p.stem: p for p in PROJECT.glob("formal/**/*.lean")}
    owners.update({p.stem: p for p in files if p.suffix == ".lean"})
    todo = [p for p in files if p.suffix == ".lean"]
    seen = set(todo)
    while todo:
        path = todo.pop()
        for module in re.findall(r"^\s*(?:public\s+)?import(?:\s+all)?\s+([A-Za-z0-9_.]+)",
                                 path.read_text(), re.MULTILINE):
            target = owners.get(module)
            if target is not None and target not in seen:
                seen.add(target)
                files.append(target)
                todo.append(target)
    return sorted(set(files))


def snapshot_inputs(files: list[Path]) -> dict[str, str]:
    return {str(p.relative_to(PROJECT)): digest(p) for p in files}


def prepare(workspace: Path, source_files: list[Path]) -> dict[str, str]:
    workspace.mkdir(parents=True)
    for path in source_files:
        if path.is_relative_to(STUDY):
            destination = workspace / path.relative_to(STUDY)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, destination)
    config = (workspace / "lakefile.lean").read_text()
    config = config.replace('packagesDir := "../../.lake/packages"',
                            'packagesDir := ' + json.dumps(str(PROJECT / ".lake/packages")))
    config = config.replace('require mtChainLinear from "../.."',
                            'require mtChainLinear from ' + json.dumps(str(PROJECT)))
    (workspace / "lakefile.lean").write_text(config)
    manifest = json.loads((workspace / "lake-manifest.json").read_text())
    manifest["packagesDir"] = str(PROJECT / ".lake/packages")
    for package in manifest["packages"]:
        if package["name"] == "mtChainLinear":
            package["dir"] = str(PROJECT)
    dump(workspace / "lake-manifest.json", manifest)
    return {name: digest(workspace / name) for name in ("lakefile.lean", "lake-manifest.json")}


def run(command: list[str], cwd: Path, log: Path, expected_success: bool = True) -> dict:
    start = time.monotonic()
    with log.open("w") as handle:
        completed = subprocess.run(command, cwd=cwd, stdout=handle, stderr=subprocess.STDOUT,
                                   timeout=900, check=False)
    result = {"command": command, "exit_code": completed.returncode,
              "elapsed_seconds": round(time.monotonic() - start, 3),
              "log": str(log.relative_to(STUDY)), "log_sha256": digest(log)}
    if (completed.returncode == 0) != expected_success:
        raise RuntimeError(f"Unexpected exit {completed.returncode}: {log}")
    print(f"{'PASS' if expected_success else 'REJECTED'} {log.name} ({result['elapsed_seconds']} s)", flush=True)
    return result


def main() -> int:
    attempts = STUDY / ".build"
    attempts.mkdir(exist_ok=True)
    index = 1
    while (attempts / f"attempt-{index:03d}").exists():
        index += 1
    attempt = attempts / f"attempt-{index:03d}"
    attempt.mkdir()
    result = {"status": "RUNNING", "started_utc": datetime.now(timezone.utc).isoformat(),
              "attempt": str(attempt.relative_to(STUDY)), "second_kernel": "NOT_RUN"}
    try:
        files = source_inputs()
        before = snapshot_inputs(files)
        dump(attempt / "SOURCES_BEFORE.json", before)
        result["lean_version"] = subprocess.check_output(["lake", "env", "lean", "--version"],
            cwd=STUDY, text=True).strip()
        result["mathlib_revision"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=PROJECT / ".lake/packages/mathlib", text=True).strip()
        manifest = json.loads((STUDY / "lake-manifest.json").read_text())
        pinned = next(x["rev"] for x in manifest["packages"] if x["name"] == "mathlib")
        if result["mathlib_revision"] != pinned:
            raise RuntimeError("Mathlib checkout differs from pinned manifest")
        for path in (STUDY / "formal").glob("*.lean"):
            text = code_only(path.read_text())
            if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(?:public\s+)?axiom\s", text, re.MULTILINE):
                raise RuntimeError(f"Forbidden proof escape/declaration in {path}")
        workspace = attempt / "workspace"
        result["path_adaptations"] = prepare(workspace, files)
        result["build"] = run(["lake", "build", "--wfail"], workspace, attempt / "build.log")
        log_text = (attempt / "build.log").read_text()
        if re.search(r"(?:^|\n)warning:|(?:^|\n)error:", log_text):
            raise RuntimeError("Warning/error in strict build")
        audits = [json.loads(line.split(MARKER, 1)[1]) for line in log_text.splitlines() if MARKER in line]
        if len(audits) != 1:
            raise RuntimeError("Expected exactly one complete audit JSON record")
        audit = audits[0]
        names = {x["name"] for x in audit["theorems"]}
        missing = {"MTChainFormal.BiasedResampling." + x for x in REQUIRED} - names
        if missing or audit["status"] != "PASS" or not audit["old_runtime_imports_excluded"]:
            raise RuntimeError("Incomplete theorem audit: " + repr(missing))
        if not set(audit["raw_closure_axioms"]) <= ALLOWED:
            raise RuntimeError("Unexpected raw-closure axiom")
        artifacts = {}
        for owner in audit["owned_imports"]:
            olean = Path(owner["olean"])
            if not olean.is_relative_to(workspace / ".lake/build/lib/lean"):
                raise RuntimeError("Study artifact borrowed from another build: " + str(olean))
            for extension in ("", ".private", ".server"):
                artifact = Path(str(olean) + extension)
                if artifact.exists():
                    artifacts[str(artifact.relative_to(STUDY))] = digest(artifact)
        dump(attempt / "AXIOM_AUDIT.json", audit)
        result["axiom_audit"] = {"theorem_count_including_generated": audit["theorem_count"],
                                  "raw_closure_count": audit["raw_closure_count"],
                                  "axioms": audit["raw_closure_axioms"],
                                  "sha256": digest(attempt / "AXIOM_AUDIT.json")}
        result["artifacts_sha256"] = artifacts
        controls = {
            "LowBias": ('module\nimport BiasedDefinitions\nopen MTChainFormal.BiasedResampling\n'
                        'noncomputable section\n'
                        'example : AdmissibleBias := ⟨1 / 3, by constructor <;> norm_num⟩\nend\n'),
            "UniformDrift": ('module\nimport BiasedControls\nopen MTChainFormal MTChainFormal.BiasedResampling\n'
                             'example : 1 + average (1 / 3) (fun u => potential '
                             '(replace Controls.interiorWitness Controls.interiorTarget u)) ≤ '
                             'potential Controls.interiorWitness := by\n'
                             '  norm_num only [Controls.interior_uniform_average, Controls.interior_potential]\n'),
            "OmittedTactic": ('module\nimport BiasedControls\nopen MTChainFormal MTChainFormal.BiasedResampling\n'
                              'example : 1 + average (2 / 3) (fun u => Controls.thresholdScore '
                              '(replace Controls.endpointWitness Controls.endpointTarget u)) ≤ '
                              'Controls.thresholdScore Controls.endpointWitness := by\n'
                              '  norm_num only [Controls.endpoint_threshold_average, Controls.endpoint_thresholdScore]\n'),
        }
        result["negative_controls"] = {}
        for name, source in controls.items():
            path = workspace / (name + ".lean")
            path.write_text(source)
            record = run(["lake", "env", "lean", str(path)], workspace,
                         attempt / (name + ".log"), expected_success=False)
            diagnostic = (attempt / (name + ".log")).read_text()
            if "unsolved goals" not in diagnostic:
                raise RuntimeError("Control did not fail on its mathematical obligation: " + name)
            if any(marker in diagnostic for marker in
                   ("unknown module", "does not exist", "dependsOnNoncomputable", "failed to compile definition")):
                raise RuntimeError("Control failed on missing infrastructure: " + name)
            record["source_sha256"] = digest(path)
            result["negative_controls"][name] = record
        # A new axiom can pass Lean's compiler. The raw closure audit must
        # nevertheless reject its use in a theorem in the study namespace.
        poisoned = attempt / "poisoned-workspace"
        prepare(poisoned, files)
        control_file = poisoned / "formal/BiasedControls.lean"
        with control_file.open("a") as handle:
            handle.write("\nnamespace MTChainFormal.BiasedResampling\n"
                         "axiom injectedAssumption : False\n"
                         "theorem poisonedClaim : False := injectedAssumption\n"
                         "end MTChainFormal.BiasedResampling\n")
        poison_record = run(["lake", "build", "BiasedAudit"], poisoned,
                            attempt / "InjectedAxiom.log", expected_success=False)
        if "Forbidden transitive axiom" not in (attempt / "InjectedAxiom.log").read_text():
            raise RuntimeError("Injected axiom was not rejected by the raw closure auditor")
        poison_record["source_sha256"] = digest(control_file)
        result["negative_controls"]["InjectedAxiom"] = poison_record
        after = snapshot_inputs(files)
        dump(attempt / "SOURCES_AFTER.json", after)
        if before != after:
            raise RuntimeError("Live proof/source inputs changed during replay")
        result.update(status="PASS", source_inputs_sha256=before, source_inputs_unchanged=True,
                      finished_utc=datetime.now(timezone.utc).isoformat())
    except Exception as error:
        result.update(status="FAIL", error=str(error), finished_utc=datetime.now(timezone.utc).isoformat())
    dump(attempt / "RESULT.json", result)
    dump(STUDY / "RESULT.json", result)
    print(json.dumps({k: result[k] for k in ("status", "attempt", "error") if k in result}), flush=True)
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
