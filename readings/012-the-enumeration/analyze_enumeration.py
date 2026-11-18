#!/usr/bin/env python3
"""usage: analyze_enumeration.py <raw dir>
The table of heartbeats by rise and level, whether every run agrees, and for each rise the floor and the slope of the
reading against the area under the levels, n(n+1)/2, in heartbeats and in blanks."""
import sys, os, re
rows = {}
for line in open(os.path.join(sys.argv[1], "readings.out")):
    m = re.search(r"READ rise=(\d+) level=(\d+) cells=(\d+) beat=(\d+) blank=(\d+)", line)
    if m: rows.setdefault((int(m.group(1)), int(m.group(2))), []).append((int(m.group(4)), int(m.group(5))))
    elif "error" in line: print("ERROR:", line.strip()[:200])
same = all(len(set(v)) == 1 for v in rows.values())
print("readings:", len(rows), "identical across runs:", same)
rises = sorted({k[0] for k in rows}); levels = sorted({k[1] for k in rows})
blank = sorted({v[0][1] for v in rows.values()})
print("blank beside every reading:", blank)
print("level   " + "".join(f"rise {c:>8}" for c in rises))
for n in levels:
    print(f"{n:>5}   " + "".join(f"{rows[(c, n)][0][0]:>13}" for c in rises))
def fit(xs, ys):
    k = len(xs); mx = sum(xs) / k; my = sum(ys) / k
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    a = my - b * mx
    ss = sum((y - (a + b * x)) ** 2 for x, y in zip(xs, ys)); st = sum((y - my) ** 2 for y in ys)
    return a, b, 1 - ss / st
B = blank[0]
print("rise   floor(hb)  floor/blank  slope(hb per unit area)  slope/rise   R2    level 0 read")
for c in rises:
    xs = [n * (n + 1) // 2 for n in levels]; ys = [rows[(c, n)][0][0] for n in levels]
    a, b, r2 = fit(xs, ys)
    print(f"{c:>4}   {a:>9.0f}  {a / B:>10.3f}  {b:>22.1f}  {b / c:>10.1f}  {r2:.5f}  {rows[(c, 0)][0][0]:>8}")
