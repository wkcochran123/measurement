# 010 — The value from the nanoseconds

Episode 8's section computes the printed value from six tapes through one reader, `List.length`. This experiment puts
a clock where the count stood: each tape is read by clicking every cell once, timed, and the value is computed from the
polynomial directly with each count replaced by a measured ratio to one blank.

- `probe_epsilon.lean`, `probe_gauss.lean`, `probe_coefficient.lean`, `probe_reading.lean`, `probe_memory.lean`,
  `probe_description.lean`: the six tapes Episode 8's reader is handed (18, 5, 13, 2, 18 and 106 cells).
- `probe_one_blank.lean`: a tape of one cell, the device's truth. `probe_no_tape.lean`: the empty tape.
  Output of each: `READ label hb=<heartbeats> ns=<nanoseconds>`.
- `run_ns.sh <CARD_2> <this folder> <runs>`; `analyze_ns.py <raw dir>`; `probes.list`.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below.

Observable: nanoseconds and heartbeats of elaborating a term and reducing it to weak head normal form, by the two lines
of `the_ekg_reads` (Episode 8), on the term alone.

Source: `10a1184`. Status: read on the M2 (`raw/M2/`); see READINGS, Experiment 010. All probes compiled as sealed.

## The seal

```
Experiment 010, the value from the nanoseconds. Sealed Tue Nov 17 11:35:18 EST 2026, before any output of these probes was read.
The probes were not executed before sealing; only the six tape names were checked to resolve, in a separate file. If a
probe fails to compile, the repair is reported with the readings, and a repair that changes what is measured voids the
seal for that probe.

The author's statement, 17 November 2026: "now, the experiment is to use the nanoseconds to compute the value using the
polynomial directly. that should read _slightly_ high, lol....." And, earlier the same day: "the length is one blank."

The polynomial. Episode 8's section reads six tapes through one reader, and the printed value is
    (e*e/g) * (b*m + sqrt((b*m)^2 - 4*a*m)) / (2*a)
with e, g, a, b, m the reader's value on the epsilon tape, Gauss's, the coefficient tape, the basis' reading and the
memory tape. With the reader List.length these are 18, 5, 13, 2, 18 and the value is 137.011290... The sixth tape, the
description, 106 cells, enters only where the crank starts and is read here and not used.

The measurement. For each tape, one fresh process elaborates and reduces to weak head normal form a term that clicks
every cell of the tape once, by the two lines of Episode 8's EKG, with a clock read before and after: heartbeats and
nanoseconds. Two more probes: a tape of one cell holding the device's truth (one blank), and no tape. Ten runs,
interleaved. Source: 10a1184. Machine: Apple M2.

The rules, fixed here. The value is computed from the formula above, directly, with each of e, g, a, b, m replaced by:
  A. the tape's median nanoseconds over the one blank's median nanoseconds;
  B. the tape's heartbeats over the one blank's heartbeats;
  C, D (recorded, not sealed). the same two, each net of the reading of no tape.

S1. Heartbeat counts are identical across the ten runs of every probe.
S2. (rule A, the nanoseconds.) Two rules, which exclude each other:
      AUTHOR  as Claude takes it, and the author may correct it: the value reads slightly high: greater than
              137.011290 and less than 138.381403 (within one part in a hundred above).
      CLAUDE  it does not: either the discriminant is negative and there is no value, or the value is outside
              135.641177 to 138.381403 (more than one part in a hundred away, either side). The formula is not
              homogeneous in the reader: a reader that is off by one part in a hundred on every tape moves the value by
              about three, and below 0.85 of the counts there is no real root.
S3. (rule B, the heartbeats.) CLAUDE: the same as S2 CLAUDE: no value, or a value more than one part in a hundred from
    137.011290.
S4. CLAUDE: the heartbeats of the five tapes used are not in the ratio of their cells to the one blank: the cells of
    these tapes are not the device's truth, and 009b found the device's truth to cost more than any other fact.

Would refute: S1, any two runs of a probe that differ in heartbeats. S2, each rule by the other's outcome; a value
below 137.011290 and within one part in a hundred refutes both and is reported as found. S3 and S4, the contrary.
```
