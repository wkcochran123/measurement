#!/usr/bin/env python3
"""usage: analyze_boot.py <output of run_boot.sh> ...

For each file: the blanks, and for each loop its kind, its first-turn heartbeats and the set of counts on later turns."""
import sys

def runs(path):
    out, cur = [], None
    for line in open(path):
        w = line.strip().split("info: ")[-1].split()
        if not w:
            continue
        if w[0] == "RUN":
            cur = {"blank": [], "loops": {}}
            out.append(cur)
        elif cur is None:
            continue
        elif w[0] == "BLANK":
            cur["blank"].append(int(w[2]))
        elif w[0] == "TURN":
            cur["loops"].setdefault((int(w[1]), w[2]), []).append(int(w[4]))
    return out

for path in sys.argv[1:]:
    R = runs(path)
    same = all(r == R[0] for r in R)
    print(path)
    print("  runs: %d, heartbeat counts identical across runs: %s" % (len(R), same))
    print("  blanks:", R[0]["blank"])
    for (n, kind), h in sorted(R[0]["loops"].items()):
        print("  loop %d %-8s turns %d, first turn %d, later turns %s, total %d" % (n, kind, len(h), h[0], sorted(set(h[1:])), sum(h)))
