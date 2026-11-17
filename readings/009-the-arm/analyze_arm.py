#!/usr/bin/env python3
"""usage: analyze_arm.py <raw dir>
For each probe: whether the runs are identical, the blank, and each read as  pass arm beat blank."""
import sys, glob, os
for path in sorted(glob.glob(os.path.join(sys.argv[1], "probe_*.out"))):
    runs, cur = [], None
    for line in open(path):
        w = line.strip().split("info: ")[-1].split()
        if not w: continue
        if w[0] == "RUN": cur = []; runs.append(cur)
        elif cur is not None and w[0] in ("BLANK", "READ"): cur.append(tuple(w))
        elif "error" in line: print(path, "ERROR:", line.strip()[:160])
    if not runs: print(path, "no runs"); continue
    print(os.path.basename(path), "runs", len(runs), "identical", all(r == runs[0] for r in runs))
    for w in runs[0]:
        print("   ", " ".join(w))
