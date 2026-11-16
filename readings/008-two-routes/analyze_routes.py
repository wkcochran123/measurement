#!/usr/bin/env python3
"""usage: analyze_routes.py <halving-first output> <crank-first output>

Reads the output of run_routes.sh for the two probes and reports each sealed item."""
import sys

def runs(path):
    out, cur = [], None
    for line in open(path):
        line = line.strip()
        if line.startswith("RUN "):
            cur = {"HALVING": [], "CRANK": [], "MEET": None, "BLANK": None}
            out.append(cur)
            continue
        if cur is None:
            continue
        line = line.split("info: ")[-1] if "info: " in line else line
        w = line.split()
        if not w:
            continue
        if w[0] == "BLANK":
            cur["BLANK"] = (int(w[1]), int(w[2]))
        elif w[0] in ("HALVING", "CRANK"):
            cur[w[0]].append((int(w[2]), int(w[3])))
        elif w[0] == "MEET":
            cur["MEET"] = (w[1], w[2])
    return out

def mean(xs):
    return sum(xs) / len(xs)

first, second = runs(sys.argv[1]), runs(sys.argv[2])
everything = first + second
ref = everything[0]

same = all(r[k] and [h for h, _ in r[k]] == [h for h, _ in ref[k]] for r in everything for k in ("HALVING", "CRANK"))
print("(a) counts identical across runs and orders:", same)
print("(b) both routes meet the build's:", all(r["MEET"] == ("true", "true") for r in everything))

H = sum(h for h, _ in ref["HALVING"])
C = sum(h for h, _ in ref["CRANK"])
gap = abs(H - C) / max(H, C)
print("    halving total %d, crank total %d, blank %d" % (H, C, ref["BLANK"][0]))
print("(c) account A, totals equal within 1%%: %s (difference %.2f%%)" % (gap <= 0.01, 100 * gap))
print("(d3) account B, totals differ by more than 1%%: %s" % (gap > 0.01))

h = [x for x, _ in ref["HALVING"]][3:]
flat = (max(h) - min(h)) / mean(h)
print("(d1) halving heartbeats flat after step 3 (spread <= 10%% of mean): %s (spread %.1f%%)" % (flat <= 0.10, 100 * flat))

n = len(ref["HALVING"])
third = n // 3
early = mean([mean([r["HALVING"][i][1] for r in everything]) for i in range(3, third)])
late = mean([mean([r["HALVING"][i][1] for r in everything]) for i in range(n - third, n)])
print("(d2) halving wall time grows (last third > first third): %s (%.0f ns against %.0f ns)" % (late > early, late, early))
