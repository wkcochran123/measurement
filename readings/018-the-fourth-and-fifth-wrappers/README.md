# 018 — The fourth and fifth wrappers

Explained in `READINGS.md` (repo root), section "Experiment 018".

- `SEALED_PREDICTION.txt`: written before any run.
- `probe.py`: writes one probe a reading; every probe defines all five cards alike and imports only Episode 12.
- `run.sh`: one fresh process a reading, Lean capped at 1500 MB; output in `raw/M2/`.
- Requires the built oleans: `cd CARD_2 && lake build Measurement.Episode12`.

Before sealing, the scaffolding and the two measured terms were type-checked once at depth one with `#check`, no meter
read; no reading of these probes has been taken.
