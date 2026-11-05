"""Offline boot347 source-bound time association and historical diagnostics.

Only Python standard-library modules are used. No research module is imported.
Clock intervals below are empirical compatibility intervals, not timing proofs.
"""

import argparse
import ast
import csv
from datetime import datetime, timedelta, timezone
from decimal import Decimal
import hashlib
import json
import math
from pathlib import Path
import re
import statistics


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.write("\n")


def diagnostics(rows, cols):
    result = {}
    night = [r for r in rows if r["elevation"] < -3]
    overlap = [r for r in rows if -4 <= r["elevation"] <= 0]
    narrow = [r for r in rows if -4 < r["elevation"] < -2]
    cloud = [r for r in rows if -5 < r["elevation"] < 10]
    zone = [r for r in rows if -3 < r["elevation"] < 8]

    def record(name, count, minimum, passed=None, **metrics):
        status = "N/A" if count < minimum or passed is None else "PASS" if passed else "FAIL"
        result[name] = dict(status=status, eligible_rows=count, minimum_rows=minimum, **metrics)

    if len(night) >= 20:
        stds = [statistics.pstdev(r[c] for r in night) for c in cols]
        noise = max(min(stds), 0.1)
        record("OBS", len(night), 20, any(s > 2 for s in stds),
               responsive_channels=sum(s > 2 for s in stds), max_std=max(stds))
        record("MRG", len(night), 20, max(stds) / noise > 1,
               max_snr=max(stds) / noise, noise_floor=noise)
    else:
        record("OBS", len(night), 20)
        record("MRG", len(night), 20)
    if len(overlap) >= 10:
        fraction = sum(r["lux"] > 0 for r in overlap) / len(overlap)
        std = max(statistics.stdev(r[c] for r in overlap) for c in cols)
        record("DATL", len(overlap), 10, fraction > 0.3 and std > 1,
               intensity_fraction=fraction, max_sample_std=std)
    else:
        record("DATL", len(overlap), 10)
    if len(narrow) >= 5:
        active = sum(sum(r[c] for c in cols) > 10 and r["geo_kappa"] < 100 for r in narrow)
        record("C14", len(narrow), 5, active == len(narrow), dual_active=active)
    else:
        record("C14", len(narrow), 5)
    if len(cloud) >= 10:
        std = statistics.stdev(r["cloud_cover"] for r in cloud)
        record("C19", len(cloud), 10, std < 20, cloud_sample_std=std)
    else:
        record("C19", len(cloud), 10)
    if len(zone) >= 60:
        size = len(zone) // 3
        spectra = []
        for i in range(3):
            chunk = zone[i * size:(i + 1) * size]
            means = [max(statistics.fmean(r[c] for r in chunk), 1e-8) for c in cols]
            spectra.append([x / sum(means) for x in means])
        first = [b - a for a, b in zip(spectra[0], spectra[1])]
        second = [b - a for a, b in zip(spectra[1], spectra[2])]
        norms = [math.sqrt(sum(v * v for v in vec)) for vec in (first, second)]
        if min(norms) < 1e-10:
            record("GEN", len(zone), 60, reason="Zero-norm velocity vector")
        else:
            cosine = sum(a * b for a, b in zip(first, second)) / (norms[0] * norms[1])
            record("GEN", len(zone), 60, cosine > 0, signed_cosine=cosine,
                   ignored_remainder_rows=len(zone) % 3)
    else:
        record("GEN", len(zone), 60)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    plan_path = base / "PLAN.json"
    plan = json.loads(plan_path.read_text())
    root = Path(plan["source_root"])
    for item in plan["inputs"]:
        assert digest(root / item["path"]) == item["sha256"], item["path"]
    args.output.mkdir(parents=True, exist_ok=False)
    started = datetime.now(timezone.utc).isoformat()

    serial = root / "boot347_dawn_serial.txt"
    csv_path = root / "Paper3_Final_Dataset/boot347_dawn.csv"
    cols = None
    for node in ast.parse((root / "cert_runner/utils/common.py").read_text()).body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "SPEC_COLS" for t in node.targets):
            cols = ast.literal_eval(node.value)
    assert len(cols) == 10
    with csv_path.open(newline="") as stream:
        rows = []
        for line, raw in enumerate(csv.DictReader(stream), 2):
            row = {k: float(v) for k, v in raw.items()}
            assert all(math.isfinite(v) for v in row.values())
            row.update(physical_line=line, exact_timestamp=Decimal(raw["timestamp"]))
            rows.append(row)
    assert all(a["exact_timestamp"] < b["exact_timestamp"] for a, b in zip(rows, rows[1:]))
    assert {r["boot_counter"] for r in rows} == {347.0}

    prefix = re.compile(plan["rules"]["prefix_regex"])
    events, multi = [], []
    lines = serial.read_text().splitlines()
    for line_number, line in enumerate(lines, 1):
        matches = list(prefix.finditer(line))
        if len(matches) > 1:
            multi.append(dict(physical_line=line_number, prefixes=len(matches)))
        for i, match in enumerate(matches):
            end = matches[i + 1].start() if i + 1 < len(matches) else len(line)
            body = line[match.end():end]
            events.append(dict(index=len(events), physical_line=line_number,
                               column=match.start() + 1, level=match[1],
                               uptime_ms=int(match[2]), body=body,
                               fragmented_line=len(matches) > 1))
    syncs = []
    for event in events:
        m = re.search(r"Time synchronized: (\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) \(CEST\)", event["body"])
        if m:
            epoch = int(datetime.strptime(m[1], "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone(timedelta(hours=2))).timestamp())
            syncs.append(dict(event_index=event["index"], physical_line=event["physical_line"],
                              epoch_second=epoch, uptime_ms=event["uptime_ms"],
                              offset=str(Decimal(epoch) - Decimal(event["uptime_ms"]) / 1000)))
    assert syncs, "No explicit clock synchronization; cannot proceed"
    active = events[syncs[0]["event_index"]:]
    anchors = []
    for event in active:
        m = re.search(r"SPECTRUM received: time=(\d+), valid=(\d+)", event["body"])
        if not m:
            continue
        plausible = [int(v) for v in m.groups() if 1_000_000_000 < int(v) < 3_000_000_000]
        assert len(plausible) == 1, "Ambiguous sensor epoch fields"
        epoch = plausible[0]
        offset = Decimal(epoch) - Decimal(event["uptime_ms"]) / 1000
        anchors.append(dict(physical_line=event["physical_line"], event_index=event["index"],
                            uptime_ms=event["uptime_ms"], epoch=epoch, offset=str(offset),
                            original_time_field=int(m[1]), original_valid_field=int(m[2])))
    offsets = [Decimal(a["offset"]) for a in anchors]
    low, high, median = min(offsets), max(offsets), statistics.median(offsets)
    segments, gaps, backwards = [[]], [], []
    for event in active:
        if segments[-1]:
            previous = segments[-1][-1]
            delta = event["uptime_ms"] - previous["uptime_ms"]
            if delta < 0:
                backwards.append(dict(before_line=previous["physical_line"], after_line=event["physical_line"], delta_ms=delta))
            if delta > 30000 or delta < -1000:
                gaps.append(dict(before_line=previous["physical_line"], after_line=event["physical_line"],
                                 before_uptime_ms=previous["uptime_ms"], after_uptime_ms=event["uptime_ms"],
                                 delta_ms=delta, within_same_physical_line=previous["physical_line"] == event["physical_line"]))
                segments.append([])
        event["segment_id"] = len(segments) - 1
        segments[-1].append(event)

    def brief(event):
        if event is None:
            return None
        return {k: event[k] for k in ("physical_line", "column", "uptime_ms", "segment_id")}

    def row_brief(row):
        if row is None:
            return None
        return dict(physical_line=row["physical_line"], timestamp=str(row["exact_timestamp"]),
                    pwm=row["pwm_percent"], cct=row["cct_sent"], elevation=row["elevation"])

    commands, geos, hues = [], [], []
    for event in active:
        m = re.search(r"Sent ACTUATOR_CMD: node=(\d+), pwm=(\d+)%, cct=(\d+)K", event["body"])
        if m:
            commands.append(dict(**brief(event), event_index=event["index"], node=int(m[1]), pwm=int(m[2]), cct=int(m[3])))
        if "GEO_PERTURB:" in event["body"]:
            m = re.search(r"PWM=(\d+)%", event["body"])
            assert m
            geos.append(dict(**brief(event), event_index=event["index"], pwm=int(m[1]), text=event["body"]))
        m = re.search(r"hue_client: Light (\d+): (\d+)% @ (\d+)K", event["body"])
        if m:
            hues.append(dict(**brief(event), event_index=event["index"], pwm=int(m[2]), cct=int(m[3])))

    segment_results = []
    for sid, segment in enumerate(segments):
        first, last = segment[0], segment[-1]
        left = Decimal(first["uptime_ms"]) / 1000 + high
        right = Decimal(last["uptime_ms"]) / 1000 + low
        selected = [r for r in rows if left <= r["exact_timestamp"] <= right]
        segment_results.append(dict(segment_id=sid, first=brief(first), last=brief(last),
            duration_seconds=(last["uptime_ms"] - first["uptime_ms"]) / 1000,
            empirical_csv_interval=[str(left), str(right)],
            csv_physical_lines=[r["physical_line"] for r in selected], csv_rows=len(selected),
            observed_sent_commands=sum(c["segment_id"] == sid for c in commands),
            geo_lines=[g["physical_line"] for g in geos if g["segment_id"] == sid],
            diagnostics=diagnostics(selected, cols)))

    joins = []
    for geo in geos:
        possible = [c for c in commands if c["segment_id"] == geo["segment_id"] and
                    c["event_index"] > geo["event_index"] and 0 <= c["uptime_ms"] - geo["uptime_ms"] <= 5000]
        command = possible[0] if possible else None
        possible_hue = [h for h in hues if h["segment_id"] == geo["segment_id"] and
                        h["event_index"] > geo["event_index"] and 0 <= h["uptime_ms"] - geo["uptime_ms"] <= 5000]
        hue = possible_hue[0] if possible_hue else None
        left = Decimal(geo["uptime_ms"]) / 1000 + low
        right = Decimal(geo["uptime_ms"]) / 1000 + high
        prior = [r for r in rows if r["exact_timestamp"] < left]
        after = [r for r in rows if r["exact_timestamp"] > right]
        ambiguous = [r for r in rows if left <= r["exact_timestamp"] <= right]
        nearby = [r for r in rows if command and r["pwm_percent"] == command["pwm"] and
                  r["cct_sent"] == command["cct"] and left - 18 <= r["exact_timestamp"] <= right + 18]
        candidates = []
        for row in nearby:
            relationship = "BEFORE" if row["exact_timestamp"] < left else "AFTER" if row["exact_timestamp"] > right else "AMBIGUOUS"
            candidates.append(dict(**row_brief(row), temporal_relation=relationship))
        joins.append(dict(geo=geo, sent_command=command, hue_record=hue,
            payloads_agree=bool(command and hue and geo["pwm"] == command["pwm"] == hue["pwm"] and command["cct"] == hue["cct"]),
            empirical_epoch_interval=[str(left), str(right)],
            last_before=row_brief(prior[-1] if prior else None), first_after=row_brief(after[0] if after else None),
            time_ambiguous_csv_rows=[row_brief(r) for r in ambiguous],
            matching_tuple_candidates_within_18_seconds=candidates,
            first_after_tuple_matches=bool(command and after and after[0]["pwm_percent"] == command["pwm"] and after[0]["cct_sent"] == command["cct"]),
            association_status="EMPIRICAL_COMPATIBILITY_ONLY; CAUSAL_RESPONSE_UNKNOWN"))

    body_anchors = dict(anchors=anchors, syncs=syncs, min_offset=str(low), max_offset=str(high), median_offset=str(median),
                        status="EMPIRICAL; NOT_A_PROVED_CLOCK_OR_LATENCY_BOUND")
    write_json(args.output / "CLOCK.json", body_anchors)
    write_json(args.output / "GAPS.json", dict(gaps=gaps, backwards=backwards, multiprefix_lines=multi))
    write_json(args.output / "SEGMENTS.json", segment_results)
    write_json(args.output / "COMMANDS.json", commands)
    write_json(args.output / "GEO_JOINS.json", joins)
    longest = max(segment_results, key=lambda s: s["duration_seconds"])
    covered = {line for s in segment_results for line in s["csv_physical_lines"]}
    counts = {name: {status: sum(s["diagnostics"][name]["status"] == status for s in segment_results)
                     for status in ("PASS", "FAIL", "N/A")} for name in ("OBS", "MRG", "DATL", "C14", "C19", "GEN")}
    summary = dict(status="OFFLINE_REPLAY_COMPLETE; INTEGRATED_PPG_REPAIR_NOT_ESTABLISHED",
        started_utc=started, finished_utc=datetime.now(timezone.utc).isoformat(),
        plan_sha256=digest(plan_path), executor_sha256=digest(Path(__file__)), source_pins=plan["inputs"],
        csv_rows=len(rows), serial_physical_lines=len(lines), parsed_timestamped_records=len(events),
        multiprefix_lines=len(multi), spectrum_epoch_anchors=len(anchors),
        observed_gaps_over_30_seconds=sum(g["delta_ms"] > 30000 for g in gaps),
        segments=len(segments), empirical_interior_csv_rows=len(covered),
        unassigned_csv_rows=len(rows) - len(covered), observed_commands=len(commands), geo_events=len(geos),
        longest_segment=longest, whole_boot_diagnostics=diagnostics(rows, cols), segment_status_counts=counts,
        matched_next_samples=sum(j["first_after_tuple_matches"] for j in joins),
        limitations=["Empirical clock envelope is not a proven true-time bound",
                     "No observed gap does not establish capture completeness",
                     "Sample timestamp semantics and unrecorded intervening commands remain unresolved",
                     "Window diagnostics do not inherit full-log certificate meaning or the formal8localplan contract",
                     "No physical repair, PPG acceptance, MT process or practical advantage established"])
    for item in plan["inputs"]:
        assert digest(root / item["path"]) == item["sha256"], "Input changed during replay"
    summary["source_hashes_unchanged"] = True
    write_json(args.output / "RESULT.json", summary)
    print(json.dumps({k: summary[k] for k in ("status", "csv_rows", "serial_physical_lines", "parsed_timestamped_records", "multiprefix_lines", "spectrum_epoch_anchors", "observed_gaps_over_30_seconds", "segments", "empirical_interior_csv_rows", "observed_commands", "geo_events", "matched_next_samples", "segment_status_counts")}, indent=2))


if __name__ == "__main__":
    main()
