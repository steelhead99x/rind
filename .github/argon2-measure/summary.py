#!/usr/bin/env python3
"""Median of each round's criterion median, spread, and ratio to a base config."""
import json, os, statistics, sys
out, base = sys.argv[1], sys.argv[2]
cfgs = [l.split("\t")[0] for l in open(os.path.join(out, "configs.tsv"))]
rows = {}
for c in cfgs:
    for r in sorted(os.listdir(os.path.join(out, c))):
        crit = os.path.join(out, c, r, "criterion")
        for g in sorted(os.listdir(crit)):
            if not g.startswith("argon2id-"): continue
            for f in sorted(os.listdir(os.path.join(crit, g))):
                p = os.path.join(crit, g, f, "new", "estimates.json")
                if os.path.exists(p):
                    ns = json.load(open(p))["median"]["point_estimate"]
                    rows.setdefault((g, f, c), []).append(ns)
print(f"| size | lib | config | runs (ms) | median ms | spread | {base} rind / this |")
print("|---|---|---|---|---|---|---|")
for (g, f, c), v in sorted(rows.items()):
    med = statistics.median(v)
    spread = (max(v) - min(v)) / med * 100
    b = rows.get((g, "rind", base))
    ratio = f"{statistics.median(b) / med:.3f}x" if b else ""
    print(f"| {g[9:]} | {f} | {c} | {', '.join(f'{x/1e6:.1f}' for x in v)} | {med/1e6:.2f} | {spread:.1f}% | {ratio} |")
