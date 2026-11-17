#!/usr/bin/env python3
"""Median of each round's criterion median, spread, and ratios to the base
config's rind time and to RustCrypto's time in the same runs."""
import json, os, statistics, sys
out, base = sys.argv[1], sys.argv[2]
cfgs = [l.split("\t")[0] for l in open(os.path.join(out, "configs.tsv"))]
rows = {}
for c in cfgs:
    for r in sorted(os.listdir(os.path.join(out, c))):
        crit = os.path.join(out, c, r, "criterion")
        if not os.path.isdir(crit): continue
        for g in sorted(os.listdir(crit)):
            if not g.startswith("argon2id-"): continue
            for f in sorted(os.listdir(os.path.join(crit, g))):
                p = os.path.join(crit, g, f, "new", "estimates.json")
                if os.path.exists(p):
                    rows.setdefault((g, f, c), []).append(json.load(open(p))["median"]["point_estimate"])
# RustCrypto does not change with rind's config: pool its runs across configs.
rc = {}
for (g, f, c), v in rows.items():
    if f == "rustcrypto": rc.setdefault(g, []).extend(v)
print(f"| size | lib | config | runs (ms) | median ms | spread | vs portable ({base}) | vs RustCrypto |")
print("|---|---|---|---|---|---|---|---|")
for g in sorted({k[0] for k in rows}):
    for c in cfgs:
        v = rows.get((g, "rind", c))
        if not v: continue
        med = statistics.median(v); b = statistics.median(rows[(g, "rind", base)])
        print(f"| {g[9:]} | rind | {c} | {', '.join(f'{x/1e6:.2f}' for x in v)} | {med/1e6:.2f} | {(max(v)-min(v))/med*100:.1f}% | {b/med:.3f}x | {statistics.median(rc[g])/med:.3f}x |")
    v = rc[g]; med = statistics.median(v)
    print(f"| {g[9:]} | rustcrypto | all runs | {len(v)} runs | {med/1e6:.2f} | {(max(v)-min(v))/med*100:.1f}% | {statistics.median(rows[(g, 'rind', base)])/med:.3f}x | 1.000x |")
