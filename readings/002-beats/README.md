# 002 — Beats: the third clock inferred from two

Two machines run the same device work at different rates. Summed, two clocks of rates f1 and f2 make a carrier at the
mean rate and an envelope whose extremes recur at the beat rate |f1 - f2|: the moments both frames read the same phase,
a clock neither machine carries. This experiment counts those extremes.

- `gen_beats.py K C`: a Lean file that elaborates K device decisions of C cells, each shifted by k so every term is new
  (cold), logging per step `BEAT k raw blank ns` on Episode 8's meter.
- `run_beats.sh <CARD_2 dir> <probe> <runs>`: the runs on one machine.
- `analyze_beats.py <A> <B>`: checks the heartbeat sequences agree; computes the fringe order F(t) = H_B(t) - H_A(t) at
  equal wall time, its slope (the beat frequency), and heartbeats per extreme, with the spread over all run pairings.
- `SEALED_PREDICTION.txt`: written before the runs.

Resolution: one sample per step (about 130,000 heartbeats) cannot resolve one fringe (about 22 heartbeats); F is the
fringe count, as an interferometer's counter reads it. Requires built `Measurement.Episode12` oleans.
