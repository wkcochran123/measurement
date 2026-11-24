# 019 — The Borwein receipts

Explained in `READINGS.md` (repo root), section "Experiment 019".

- `SEALED_PREDICTION.txt`: written before any run (Claude's).  `SEALED_PREDICTION_AUTHOR.txt`: the author's, in Claude's operational
  reading, also before any run; none has been read.
- `probe.py`: writes one probe a reading; every probe imports only Episode 13 and elaborates one theorem command.
- `run.sh`: one fresh process a reading, Lean capped at 1500 MB, 300 s each; output in `raw/M2/`.
- Requires the built oleans: `cd CARD_2 && lake build Measurement.Episode13`.

Before sealing, the scaffolding was type-checked once (`probe.py check`, two `#check`s, no meter read); no reading of
these probes has been taken.
