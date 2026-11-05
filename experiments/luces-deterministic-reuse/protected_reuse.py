"""Producer-only diagnostic of fixed GEN/dataset reuse on unchanged CSVs."""

import hashlib
import json
from pathlib import Path
import sys
from time import perf_counter


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    base = Path(__file__).resolve().parent
    plan = json.loads((base / "PLAN.json").read_text())
    for item in plan["inputs"]:
        if sha(Path(item["path"])) != item["sha256"]:
            raise ValueError("Changed input")
    sys.path.insert(0, plan["source_root"])
    import pandas as pd
    from cert_runner.certs.pp_graph import c_gen
    from cert_runner.certificate_contracts import snapshot_checks

    banks = json.loads((base / "evidence/runtime-002/BANKS.json").read_text())
    frames = [pd.read_csv(Path(plan["dataset_root"]) / bank["name"]) for bank in banks]
    records = {}
    for arm in ("FIXED_VIEW_REUSE", "RECOMPUTE_PROTECTED"):
        cache, calls, decisions = {}, 0, []
        start = perf_counter()
        for b, bank in enumerate(banks):
            path = Path(plan["dataset_root"]) / bank["name"]
            for i in range(5):
                for j in range(5):
                    if i == j:
                        continue
                    if arm == "RECOMPUTE_PROTECTED" or b not in cache:
                        status, gen, _ = c_gen(frames[b])
                        if status == "N/A":
                            raise ValueError("Unavailable GEN")
                        cache[b] = (float(gen), int(sha(path), 16))
                        calls += 1
                    gen, key = cache[b]
                    if gen != bank["generator_cos"] or key != bank["dataset_key"]:
                        raise ValueError("Protected producer changed")
                    state = dict(bank["candidates"][j]["snapshot"], generator_cos=gen, dataset_key=key)
                    accepted = all(c.evaluate(state) for c in snapshot_checks(key))
                    if accepted != all(bank["candidates"][j]["checks"]):
                        raise ValueError("Acceptance changed")
                    decisions.append(accepted)
        records[arm] = dict(protected_producer_calls=calls, proposals=len(decisions),
                            accepted=sum(decisions), seconds=perf_counter() - start,
                            decisions=decisions)
    if records["FIXED_VIEW_REUSE"]["decisions"] != records["RECOMPUTE_PROTECTED"]["decisions"]:
        raise ValueError("Producer reuse changes outcomes")
    for item in plan["inputs"]:
        if sha(Path(item["path"])) != item["sha256"]:
            raise ValueError("Input changed during diagnostic")
    result = dict(status="PASS_PRODUCER_REUSE_DIAGNOSTIC", arms=records,
                  executor_sha256=sha(Path(__file__)), plan_sha256=sha(base / "PROTECTED_REUSE_PLAN.json"),
                  banks_sha256=sha(base / "evidence/runtime-002/BANKS.json"),
                  source_hashes_unchanged=True,
                  limitations="Single ordered timing, prepared frames; ordinary dependency caching obtains same reuse. No exclusive PPG advantage or full end-to-end saving.")
    output = base / "evidence/PROTECTED_REUSE.json"
    with output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({arm: {k: v for k, v in value.items() if k != "decisions"}
                      for arm, value in records.items()}, indent=2))


if __name__ == "__main__":
    main()
