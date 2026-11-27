#!/usr/bin/env python3
"""Splits a collector capture (the ncat sink's file, or an app's .jsonl) into
one bench-report host JSON per run.

usage: tools/import-device.py CAPTURE [--out DIR]

Lines that are not rind-devbench JSON (e.g. RindBench v13's text lines in the
same capture) are skipped. A run with a final `report` line is written as the
app sent it; a run cut off before that is rebuilt from its `row` lines
(median of per-round medians) and marked status "partial". Writes
DIR/<host>-<run_id>.json. No number is invented: rows without a timing are left out.
"""
import json, os, statistics, sys

def main():
    args = sys.argv[1:]
    if not args:
        sys.exit(__doc__)
    out = "."
    if "--out" in args:
        i = args.index("--out"); out = args[i + 1]; del args[i:i + 2]
    os.makedirs(out, exist_ok=True)
    runs, cur = [], None
    for line in open(args[0], errors="replace"):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        t = d.get("t")
        if t == "start":
            cur = {"start": d, "rows": [], "report": None, "end": None}; runs.append(cur)
        elif cur is None:
            continue
        elif t == "row":
            cur["rows"].append(d)
        elif t == "report":
            cur["report"] = d["report"]
        elif t in ("done", "stopped"):
            cur["end"] = d
    for r in runs:
        s = r["start"]
        rep = r["report"]
        if rep is None:
            by = {}
            for row in r["rows"]:
                by.setdefault(row["id"], []).append(row)
            results = []
            for i, rows in by.items():
                meds = sorted(x["ns"] for x in rows if x.get("ns") is not None)
                if not meds:
                    continue
                results.append({"operation": rows[0].get("op"), "library": rows[0].get("library"), "id": i,
                                "ns": statistics.median(meds), "ns_low": meds[0], "ns_high": meds[-1],
                                "rounds": len(meds), "throughput": rows[0].get("throughput")})
            dev = s.get("device", {})
            rep = {"schema": 1, "producer": s.get("schema"), "host": dev.get("host_slug"), "commit": s.get("rind_commit"),
                   "started": s.get("started"), "cpu": dev.get("cpu"), "os": dev.get("os"), "device": dev,
                   "libraries": s.get("crates"), "status": "partial", "results": results}
        name = f"{rep.get('host') or 'device'}-{s.get('run_id', 'run')}.json".replace("/", "-")
        with open(os.path.join(out, name), "w") as f:
            json.dump(rep, f, indent=1)
        print(f"{name}: {len(rep['results'])} rows, status {rep.get('status')}, rind {str(rep.get('commit'))[:12]}")

main()
