#!/usr/bin/env python3
"""usage: analyze_ns.py <raw dir>
Reads readings.out. For each tape: heartbeats (and whether every run agrees) and the median nanoseconds.
Then the value from the polynomial, with each count replaced by a measured ratio, under the sealed rules."""
import sys, os, re, statistics, math
rows = {}
for line in open(os.path.join(sys.argv[1], "readings.out")):
    m = re.search(r"RUN (\d+) .*READ (\w+) hb=(\d+) ns=(\d+)", line)
    if m: rows.setdefault(m.group(2), []).append((int(m.group(1)), int(m.group(3)), int(m.group(4))))
    elif "error" in line: print("ERROR:", line.strip()[:200])
cells = dict(epsilon=18, gauss=5, coefficient=13, reading=2, memory=18, description=106, one_blank=1, no_tape=0)
hb, ns = {}, {}
for k, v in rows.items():
    hbs = [x[1] for x in v]; nss = [x[2] for x in v]
    hb[k] = hbs[0]; ns[k] = statistics.median(nss)
    print(f"{k:12s} cells {cells[k]:3d}  hb {hbs[0]:8d} identical {len(set(hbs)) == 1}  ns median {ns[k]:10.0f}  min {min(nss)} max {max(nss)}")
def value(n):
    e, g, a, b, m = n["epsilon"], n["gauss"], n["coefficient"], n["reading"], n["memory"]
    tr = b * m; disc = tr * tr - 4 * a * m
    if disc < 0: return None, disc
    return (e * e / g) * (tr + math.sqrt(disc)) / (2 * a), disc
def show(name, n):
    v, d = value(n)
    print(f"{name}: " + ", ".join(f"{k}={n[k]:.4f}" for k in ("epsilon", "gauss", "coefficient", "reading", "memory")))
    print(f"    value = {v if v is None else round(v, 6)}   (discriminant {d:.4f}; with the counts: 137.011291, discriminant 360)")
keys = ("epsilon", "gauss", "coefficient", "reading", "memory")
show("counts (check)", {k: float(cells[k]) for k in keys})
show("rule A, ns over one blank", {k: ns[k] / ns["one_blank"] for k in keys})
show("rule B, hb over one blank", {k: hb[k] / hb["one_blank"] for k in keys})
show("rule C, ns net of no tape (recorded)", {k: (ns[k] - ns["no_tape"]) / (ns["one_blank"] - ns["no_tape"]) for k in keys})
show("rule D, hb net of no tape (recorded)", {k: (hb[k] - hb["no_tape"]) / (hb["one_blank"] - hb["no_tape"]) for k in keys})
runs = sorted({x[0] for v in rows.values() for x in v})
vals = []
for r in runs:
    try:
        n = {k: [x[2] for x in rows[k] if x[0] == r][0] / [x[2] for x in rows["one_blank"] if x[0] == r][0] for k in keys}
        vals.append(value(n)[0])
    except Exception: vals.append(None)
print("rule A, run by run:", [None if v is None else round(v, 3) for v in vals])
