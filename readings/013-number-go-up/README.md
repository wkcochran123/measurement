# 013 — Number go up

The reader can only read what is in the compile. So the timer is put in the code, and the compile says how long one
evaluation took and how long many took.

- `probe.lean`: one evaluation is the device's truth, one cell, clicked once, elaborated and reduced to weak head
  normal form. The clock and the heartbeats are read around 1, 10, 100 and 1000 of them, in one compile. Output:
  `READ evaluations=N beats=<heartbeats> nanoseconds=<nanoseconds>`.
- `run.sh <CARD_2> <this folder> <runs>`: one fresh process per run.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below.

Observable: `IO.monoNanosNow` and `withHeartbeats`, both inside the elaboration.

Source: `40da726`. Status: sealed, not yet read.

## The seal

```
Experiment 013, number go up. Sealed Wed Nov 18 17:20:35 EST 2026, before any output of the probe was read. The probe was
compiled twice with its output discarded, to see that it compiles; its first form used a field Episode 8 does not
have and was repaired to the click Experiment 012 used. No reading was seen.

The author's statements, 18 November 2026: "the reader can only read what is in the compile. so make an experiment
with the timer in the code that demonstrates that the time does increase between a single evaluation and lots of
evaluations. that's all you need, number go up."

What is asked. The timer is in the code: the probe reads the clock (nanoseconds) and the heartbeats before and after
one evaluation, and before and after ten, a hundred and a thousand of the same evaluation, in one compile. An
evaluation is the device's truth, one cell, clicked once, elaborated and reduced to weak head normal form. Five runs,
one fresh process each. Source: 40da726. Machine: Apple M2.

S1. (the author's.) In every run the nanoseconds for a thousand evaluations are more than the nanoseconds for one.
S2. CLAUDE: in every run the nanoseconds increase at every step: 1 < 10 < 100 < 1000.
S3. CLAUDE: the heartbeats increase at every step too, and are identical across the five runs; the nanoseconds are
    not identical across runs.
S4. CLAUDE: the nanoseconds for one evaluation are more than a thousandth of the nanoseconds for a thousand: the
    first evaluation costs more than a later one.
S5. Recorded, not sealed: heartbeats and nanoseconds an evaluation at each count.

Would refute: S1, any run where a thousand read no more than one. S2 to S4, the contrary, reported as found.
```
