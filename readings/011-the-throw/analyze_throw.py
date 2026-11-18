#!/usr/bin/env python3
"""usage: analyze_throw.py <raw dir>
For each probe: whether the runs are identical, and each read as  label beat blank.  Then the throws net of their controls."""
import sys, glob, os
second = {}
for path in sorted(glob.glob(os.path.join(sys.argv[1], "probe_*.out"))):
    runs, cur = [], None
    for line in open(path):
        w = line.strip().split("info: ")[-1].split()
        if not w: continue
        if w[0] == "RUN": cur = []; runs.append(cur)
        elif cur is not None and w[0] in ("BLANK", "READ"): cur.append(tuple(w))
        elif "error" in line: print(path, "ERROR:", line.strip()[:200])
    if not runs: print(path, "no runs"); continue
    print(os.path.basename(path), "runs", len(runs), "identical", all(r == runs[0] for r in runs))
    for w in runs[0]:
        print("   ", " ".join(w))
        if w[0] == "READ" and w[1] == "2": second[w[2]] = (int(w[3]), int(w[4]))
if all(k in second for k in ("sound", "sound_control", "propext", "propext_control", "truth")):
    s = second["sound"][0] - second["sound_control"][0]; p = second["propext"][0] - second["propext_control"][0]
    print("second readings:")
    print("  the throw of the sound, net of rfl:    ", s)
    print("  the throw of propext, net of rfl:      ", p)
    print("  the blank beside the sound's reading:  ", second["sound"][1])
    print("  the device's truth read as a term:     ", second["truth"][0])
    print("  the sound, whole:", second["sound"][0], " propext, whole:", second["propext"][0], " named:", second.get("named", ("-",))[0])
