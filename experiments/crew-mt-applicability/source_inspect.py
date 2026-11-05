"""Read-only source inspection with append-only query and file-hash receipts."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--reason", required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("mode", choices=["read", "search"])
    parser.add_argument("args", nargs="+")
    ns = parser.parse_args()
    start = datetime.now(timezone.utc).isoformat()
    hashes = {}
    if ns.mode == "read":
        path, lo, hi = ns.args
        p = ns.root / path
        raw = p.read_bytes()
        hashes[path] = hashlib.sha256(raw).hexdigest()
        lines = raw.decode().splitlines()
        output = "\n".join(f"{path}:{i}:{lines[i-1]}" for i in range(int(lo), min(int(hi), len(lines))+1)) + "\n"
        command = ["read_lines", path, lo, hi]
        code = 0
    else:
        pattern, *paths = ns.args
        command = ["rg", "--with-filename", "--line-number", "--ignore-case", "--glob", "*.py", pattern, *paths]
        result = subprocess.run(command, cwd=ns.root, text=True, capture_output=True)
        output = result.stdout
        code = result.returncode
        for line in output.splitlines():
            # All callers pass directories or multiple files, so rg includes paths.
            path = line.split(":", 1)[0]
            p = ns.root / path
            if p.is_file():
                hashes[path] = hashlib.sha256(p.read_bytes()).hexdigest()
    ns.out.mkdir(parents=True, exist_ok=True)
    n = len(list(ns.out.glob("query-*.json"))) + 1
    stem = ns.out / f"query-{n:03d}"
    with stem.with_suffix(".txt").open("x") as f:
        f.write(output)
    receipt = dict(reason=ns.reason, root=str(ns.root), command=command,
                   started_utc=start, ended_utc=datetime.now(timezone.utc).isoformat(),
                   returncode=code, sources=hashes,
                   output_sha256=hashlib.sha256(output.encode()).hexdigest())
    if ns.mode == "search":
        receipt["stderr"] = result.stderr
    with stem.with_suffix(".json").open("x") as f:
        json.dump(receipt, f, indent=2)
        f.write("\n")
    print(output, end="")
    if code not in (0, 1):
        raise SystemExit(code)


if __name__ == "__main__":
    main()
