#!/usr/bin/env python3
"""Verify archived extraction, active migration and standalone import boundary.

This writes a fresh source-verification receipt; it does not run Lean/Nanoda.
The optional original-project check is read-only.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from provenance import validate_sources

ROOT = Path(__file__).resolve().parents[1]
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-source", type=Path)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "evidence/migration-source-verification.json")
    args = parser.parse_args()
    result = validate_sources(ROOT, args.compare_source)["receipt"]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
