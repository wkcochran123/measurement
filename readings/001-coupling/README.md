# 001 — The coupling of the code to the implementation, and the dilation between machines

Explained in full in `READINGS.md` (repo root), section "The experiment".

- `SEALED_PREDICTION.txt`, `SEALED_PREDICTION_2.txt`: the predictions, written before the runs they predict.
- `gen.py` (cold heartbeat probe over n cells), `gen_t.py` (the same, timed), `make_probes.sh <dir>` (writes all probes).
- `run_t.sh <CARD_2 dir> <probe dir>`: ten interleaved timed repeats of n = 64 and n = 1, device and control.
- `analyze.py <timing file>...`: medians and ns per heartbeat on the device cells.
- `raw/<machine>/`: the output of each machine, committed with its row.

Sweep (heartbeats only): for each probe, `cd CARD_2 && lake env lean <probe>.lean`; one process per reading, so every reading is cold.
Requires built `Measurement.Episode12` oleans: `cd CARD_2 && lake build Measurement.Episode12`.
