# 009b — True from false

009 read three values on the four arms of `Number.le`, one step for each coin that was the true. Its true and its
false were built differently, so the step could belong to the truth or to the way the term was written. This
experiment builds a true and a false each way and reads all sixteen arms and the four clicks.

- `probe_click_T0.lean`, `_T1`, `_F0`, `_F1`: the click of one fact: a blank, the click, the click again.
- `probe_arm_X_Y.lean` for X, Y in T0, T1, F0, F1: `Number.le` on that arm.
  Output: `BLANK 0 hb`, `READ pass label beat blank`.
- `run_arm.sh <CARD_2> <this folder> <runs>`; `analyze_arm.py <raw dir>`; `probes.list`.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below and this file is what the setup commit carries.

Observable: heartbeats of elaborating a term and reducing it to weak head normal form, read by `the_ekg_reads`
(Episode 8). Baseline: the blank drawn in the same call.
What tells the readings apart: whether the numbers order by truth or by how the fact was built.

Source: `2c5e844`. Status: set up; not yet run.

## The seal

```
Experiment 009b, true from false. Sealed Tue Nov 17 09:02:00 EST 2026, before any output of these probes was read.
The probes were not executed before sealing. If a probe fails to compile, the repair is reported with the readings, and
a repair that changes what is measured voids the seal for that probe.

From 009 (setup c09cbe0, read 2258f19): on its second reading an arm of Number.le reads 15670 with no true coin, 16691
with one and 17712 with two; T,F and F,T read alike. There the true was the device's own truth and the false was a
fact built in the probe another way, so the step of 1021 might belong to the truth or to how the term was written.

The author's statement, 17 November 2026: "so, you can now tell True from False using these numbers in the ekg."

Four facts. T0: the device's truth (statement: the boolean true). F1: a false built the same way (statement: the
boolean false). F0: the false of 009 (statement: False). T1: a true built the same way (statement: True).
Twenty probes, five runs each, one fresh process per run: the click of each fact alone, and Number.le on each of the
sixteen ordered pairs of the four facts. Each probe reads a blank, the term, the term again. The meter is
the_ekg_reads of Episode 8. Source: 2c5e844.

S1. Heartbeat counts are identical across the five runs of every probe.
S2. The arm T0,F0, T0,T0, F0,F0 and F0,T0 reproduce 009's second readings: 16691, 17712, 15670, 16691.
S3. (the sixteen arms, second reading.) ADDITIVE: there are four numbers, one per fact, such that every arm reads a
    common base plus the number of its first fact plus the number of its second. In particular X,Y and Y,X read alike.
    CLAUDE holds ADDITIVE. Refuted by any arm that departs from it.
S4. (the sixteen arms, second reading.) Two rules, which exclude each other:
      AUTHOR  the meter tells the true from the false: each true's number is greater than each false's number, so
              every arm with two trues reads more than every arm with one, and those more than every arm with none.
      CLAUDE  the meter tells how the fact was built: the two facts whose statement is a boolean (T0, F1) have numbers
              greater than the two whose statement is True or False (T1, F0), whichever is true.
    If neither ordering holds, both are refuted and the four numbers are reported as found.
S5. (the four clicks alone, second reading.) The same two rules: AUTHOR, both trues read more than both falses;
    CLAUDE, T0 and F1 read more than T1 and F0.

Would refute: S1, S2, S3: any reading other than stated. S4, S5: each rule by an ordering other than its own.
What it can and cannot say. If AUTHOR holds on both S4 and S5, the meter's number decides the truth of these four
facts on this machine. That is four facts, two ways of building them, one order and one machine.
```
