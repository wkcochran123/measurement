# 003 — The calibration: heartbeats to seconds

The device's unit of work is its registered noise floor (the nowtrino's click, read at build time). The author's
declaration fixes one floor as one Compton time of the electron. Because the heartbeat count is the same on every
machine (001, 002), the conversion from heartbeats to seconds is the code's, not the machine's.

- `SEALED_RULE.txt`: the rule, written before any value was computed.
- `calibrate.py <floor>`: applies it: seconds per heartbeat; each machine's clock against the electron's (Gamma);
  the step's horizon distance.
- Reading the floor: `import Measurement.Episode12` then `#eval Measurement.Calibration.measuredFloor`, from `CARD_2/`.
- `raw/`: the floor as read on each machine's own build, and the output of `calibrate.py`.

No comparison with any measured constant is made.
