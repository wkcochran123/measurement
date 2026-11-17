# 009 — The arm

The four comparisons of the true and the false are the four arms of the device's table. Three can click and one
cannot; the author's statement of 17 November 2026 is that the three are the values of the transition matrix that
are not fixed, and that the experiment on the device should say which arm is which.

This experiment puts two of the device's own orders on the device's own meter, arm by arm.

- `probe_number_TT.lean`, `_TF`, `_FT`, `_FF`: `Number.le` on one arm: a blank, the arm, the arm again.
- `probe_number_orderA.lean`, `_orderB`, `_orderC`: all four arms, twice over, in three orders.
- `probe_abstraction_CC.lean`, `_CE`, `_EC`, `_EE`: `Abstraction.le` on one pair of compile and execute.
- `probe_abstraction_orderA.lean`, `_orderB`: all four pairs, twice over, in two orders.
  Output: `BLANK 0 hb`, `READ pass arm beat blank`.
- `run_arm.sh <CARD_2> <this folder> <runs>`; `analyze_arm.py <raw dir>`; `probes.list`.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below and this file is what the setup commit carries.

Observable: heartbeats of elaborating a term and reducing it to weak head normal form, read by `the_ekg_reads`
(Episode 8). Boundary: one call of the meter. Baseline: the blank the meter draws in the same call.
What tells the readings apart: which arm, if any, reads apart from the others on its second reading.

Source: `2c5e844` (Episodes 1 to 8 as committed; the probes import `Measurement.Episode08` and nothing later).
Status: set up; not yet run.

## The seal

```
Experiment 009, the arm. Sealed Tue Nov 17 08:54:23 EST 2026, before any output of these probes was read.
The probes were NOT executed before sealing, not even to check that they compile: a cold build of the device was
running and Episode 8 had no object file. If a probe fails to compile, the repair is reported with the readings, and
a repair that changes what is measured voids the seal for that probe.

What is read. The device's own meter, the_ekg_reads of Episode 8: the heartbeats of elaborating a term and reducing it
to weak head normal form, with the blank it draws in the same breath. Source: 2c5e844, Episodes 1 to 8 as committed.
Two orders of the device are put on the meter, arm by arm.
  number:      Number.le (Episode 1) on two numbers of one cell, whose facts are the true and the false.
               Its four arms by definition: T,T goes on to the tails; T,F is False; F,T is True; F,F is the turn.
  abstraction: Abstraction.le (Episode 3) on compile and execute.
               Its four pairs by definition: C,C true; C,E true; E,E true; E,C false.
One fresh process per run, five runs per probe. Single-arm probes read a blank, the arm, and the arm again.
Order probes read all four, twice over, in three orders (number) and two orders (abstraction).

The author's statements, 17 November 2026: "(T=T) (F=F) and one false clicks. that is 3 one false does not."
"there are _two_ bent cards that can be used to separate 3 things. a x (-c x b)." "i believe those are the values of
the transition matrix that you don't fix." "run the experiment on the device to figure out the arm."

S1. Heartbeat counts are identical across the five runs of every probe.
S2. (number, single-arm probes, the second reading of the arm.) Four rules, which exclude each other:
      AUTHOR  as Claude takes it, and the author may correct it: three values that are not fixed and one that is.
              T,F reads the least of the four, and the other three read three different values.
      CLAUDE  T,T reads apart from the other three and is the greatest, because it alone goes on to the tails;
              T,F, F,T and F,F read alike.
      PAIRS   the two sames read alike and the two differents read alike, and the two pairs differ.
      NULL    all four read alike: the meter cannot tell the arms apart, as it could not tell the routes in 008.
S3. (number) CLAUDE: the first reading of an arm in a fresh process is greater than its second, by the same amount on
    every arm (a boot, as in 008b), so S2 read on first readings gives the same rule as on second readings.
S4. (number, order probes) CLAUDE: an arm's second-pass reading does not depend on the order: each arm reads in the
    order probes what it read second in its single-arm probe.
S5. (abstraction, single-pair probes, second reading.) Rules, which exclude each other:
      CLAUDE  E,C reads apart from the other three, which read alike.
      NULL    all four read alike.
      OTHER   any other arrangement; it is recorded and it refutes both.
S6. CLAUDE: no arm of either order reads the blank on its second reading.

Would refute: S1, any probe whose runs differ. S2, each rule is refuted by an arrangement other than its own; an
arrangement that is none of the four refutes all four and is reported as found. S3, S4, S5, S6: any reading other
than stated.
What the experiment can and cannot say. It can say which arm, if any, the device's meter sets apart, and whether
three arms carry values of their own. It reads heartbeats of elaboration on one machine. It cannot say which arm is
a, b or c of the author's formula unless the arrangement singles arms out; if it does, the assignment is reported as
read and its meaning is left to the author.
```
