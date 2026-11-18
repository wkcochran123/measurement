# 014 — The two decisions

Episode 13 proves that the evidence kept of the knower's decision is the same for both decisions. The author's rule
is that the reader can only read what is in the compile, and the timer is in the compile. This experiment asks
whether the timer tells the two decisions apart.

- `probe_true_first.lean`, `probe_false_first.lean`: a blank evaluation set aside, then each decision once and a
  thousand times, in the order named. Output:
  `READ order=<o> decision=<d> evaluations=N beats=<heartbeats> nanoseconds=<nanoseconds>`.
- `run.sh <CARD_2> <this folder> <runs>`: each probe once per run, one fresh process each.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below.

Observable: `IO.monoNanosNow` and `withHeartbeats`, both inside the elaboration.

Source: `fe5cf5d`. Status: read on the M2 (`raw/M2/`); see READINGS, Experiment 014. S1 and S2 refuted, S3 confirmed.

## The seal

```
Experiment 014, the two decisions. Sealed Wed Nov 18 17:30:27 EST 2026, before any output of the probes was read. The probes
were compiled with their output discarded, to see that they compile; a namespace was opened to repair an unknown
identifier. No reading was seen.

The author's statement, 18 November 2026: "the reader can only read what is in the compile."

What is asked. Episode 13 proves that what is kept of the knower's decision (the triple, the solver's verdict, the
quartic's receipts on the root, the first component of the root's pair) is the same for both decisions, so no reader
of that evidence returns the decision. The timer is also in the compile. Does a reader of the timer tell the two
decisions apart? One evaluation is `you_re_a_daisy_if_you_do (bitFACT decision)`, elaborated and reduced to weak
head normal form. In one compile: a blank evaluation, set aside; then one decision, once and a thousand times; then
the other, once and a thousand times. Two probes, one for each order. Five runs, one fresh process per probe per run.
Source: fe5cf5d. Machine: Apple M2.

S1. CLAUDE: at a thousand evaluations the heartbeats for the decision true and for the decision false are not
    equal, and each is identical across the five runs and the two orders.
S2. CLAUDE: the decision true costs more heartbeats than the decision false. (Experiment 009b: the meter tells the
    device's own truth from everything else, and bitFACT true is FACT.Truth.)
S3. CLAUDE: the nanoseconds at a thousand evaluations do not separate the decisions: the range over the ten readings
    of one decision overlaps the range of the other.
S4. Recorded, not sealed: heartbeats and nanoseconds an evaluation, each decision, each order.

Would refute: S1, equal heartbeats, or heartbeats that change with the run or the order. S2, false costing as much
or more. S3, ranges that do not overlap. Each is reported as found.
```
