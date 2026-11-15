# 006 — Frames as points: the triangle, the box's third workload, the convective term at resolution

A triangle of single clock ratios cannot fail: ln(t1/t2) + ln(t2/t3) = ln(t1/t3) always (zero circulation). So each frame
is read on two workloads and becomes a point (ln tau_W1, ln tau_W3); three frames have a signed area, the quantity
Episode 12's `the_orientation` reads, and a nonzero area is a measured orientation. Frames: the M2 Ultra's performance
cores, its efficiency cores (a different microarchitecture, via `taskpolicy -c background`), and the M2.

- `probes/`: W1 (001's timed 64 cells and control), W2 (002's beats), W3 (005's steps), copied from their experiments.
- `run_frame.sh <CARD_2> <probes> <P|E> <w1> <w2> <w3>`: repeats per workload.
- `analyze_frames.py`: taus, (b) distinct frames, (c) the signed area with a bootstrap interval, the 3x3 interaction, and
  (d) the convective correlation from a separate 30-run file of W3 on P.
- `SEALED_PREDICTION.txt`: written first.
