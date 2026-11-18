# 012 — The enumeration

On the count the temperature is the rise times the area under the levels, for every rise. This experiment asks the
same of the meter by enumeration: twenty-eight tapes, rises 1 to 4 by levels 0 to 6, each read once. Does the floor
under the reading change with the rise?

- `probe_rise<c>_level<n>.lean`: a tape of `c * n(n+1)/2` cells of the device's truth, every cell clicked once.
  Output: `READ rise=c level=n cells=N beat=<heartbeats> blank=<heartbeats>`.
- `run_enumeration.sh <CARD_2> <this folder> <runs>`; `analyze_enumeration.py <raw dir>`; `probes.list`.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below.

Observable: heartbeats of elaborating a term and reducing it to weak head normal form, read by `the_ekg_reads`
(Episode 8). Baseline: the blank drawn in the same call.

Source: `101f871`. Status: read on the M2 (`raw/M2/`); see READINGS, Experiment 012. All probes compiled as sealed.

## The seal

```
Experiment 012, the enumeration. Sealed Wed Nov 18 07:31:27 EST 2026, before any output of these probes was read.
The probes were not put on the meter before sealing. If a probe fails to compile, the repair is reported with the
readings, and a repair that changes what is measured voids the seal for that probe.

The author's statements, 18 November 2026: "the meter's floor is also known, the input is finite, the run is finite, the
tape is finite. simple lba enumeration will provide the scaling." And: "\hbar = 1 all constants are 1 blank in size".

What is asked. Episode 13 has, on the count, that the temperature is the rise times the area under the levels, for
every rise: nothing of it stays behind when the rise is changed. On the meter the one reading taken had a floor under
its slope, and one build could not say whether the floor changes with the rise. If it does not, a proposition on the
numerical card puts the meter with the vacuum equations; if it scales with the rise, with the equations that have a
source. The enumeration: every rise from 1 to 4 and every level from 0 to 6, twenty-eight tapes, each of
rise * level(level+1)/2 cells of the device's truth, every cell clicked once, read once on Episode 8's meter beside its
blank. Three runs, one fresh process per reading. Source: 101f871. Machine: Apple M2. For each rise, the reading is
fitted against the area under the levels by least squares: its floor and its slope. Everything is also given in
blanks, the blank being the one read beside the reading.

S1. (the author's, as Claude takes it: the enumeration provides the scaling.) Every one of the twenty-eight readings is
    identical across the three runs, so that the floor and the slope at each rise are definite numbers.
S2. CLAUDE: the slope scales with the rise: slope over rise is the same at rises 1, 2, 3 and 4 to within two parts in a
    hundred.
S3. CLAUDE: the floor does not scale with the rise: the four floors agree to within five parts in a hundred, and each is
    the reading at level 0, the tape of no cells, to within five parts in a hundred. (So on the meter a part of the
    reading stays behind when the rise is changed.)
S4. CLAUDE: at each rise the reading is a straight line in the area: R squared above 0.999.
S5. Recorded, not sealed: the floor in blanks.

Would refute: S1, any two runs of a probe that differ. S2 to S4, the contrary; a floor that is proportional to the rise
refutes S3 and is reported as found.
```
