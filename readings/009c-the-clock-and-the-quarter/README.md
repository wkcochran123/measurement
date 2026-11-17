# 009c — The clock and the quarter

009b found that the meter's step of 1,021 belongs to the device's own truth, `FACT.Truth`, and to no other fact,
true or false. This experiment uses that to put a clock on the meter, and to ask whether the meter can say which of
three cards the quarter is under.

- `probe_clock_alternating.lean`: eight clicks in a row, the device's truth and a false turn about.
- `probe_clock_still_true.lean`, `probe_clock_still_false.lean`: eight clicks, the same fact every time.
- `probe_clock_plain.lean`: eight clicks, a true that is not the device's truth and a false turn about.
- `probe_card_defined_a.lean`, `_b`, `_c`: three cards with one face; what is under each, the card read by its name.
- `probe_card_named_a.lean`, `_b`, `_c`: the same three, each written out in the term that is read.
  Output: `BLANK 0 hb`, `READ tick-or-pass label beat blank`.
- `run_arm.sh <CARD_2> <this folder> <runs>`; `analyze_arm.py <raw dir>`; `probes.list`.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below and this file is what the setup commit carries.

Observable: heartbeats of elaborating a term and reducing it to weak head normal form, read by `the_ekg_reads`
(Episode 8). Baseline: the blank drawn in the same call.

Source: `2c5e844`. Status: read on the M2 (`raw/M2/`); see READINGS, Experiment 009c. All probes compiled as sealed.

## The seal

```
Experiment 009c, the clock and the quarter. Sealed Tue Nov 17 09:04:42 EST 2026, before any output of these probes was read.
The probes were not executed before sealing. If a probe fails to compile, the repair is reported with the readings, and
a repair that changes what is measured voids the seal for that probe.

From 009b (setup d9e0ab3, read 75ccdf2): on its second reading the click of the device's own truth, FACT.Truth, reads
2162; the click of a true built in the probe, and of either false, reads 1141. The step is 1021 and it belongs to the
device's truth alone.

The author's statement, 17 November 2026: "you should be able to demonstrate the clock in the device now, closing the
loop with the quarter."

The clock. Four probes, each one process reading eight clicks in a row: the device's truth and a false turn about;
the device's truth every time; a false every time; a true that is not the device's truth and a false turn about.
The quarter. Three cards with one face. Under card a the quarter stands on a false; under card b on the device's
truth; under card c on a true that is not the device's truth. Read two ways: the card defined beforehand and read by
its name, and the card written out in the term that is read, so that what is under it is named there.
Five runs per probe, one fresh process per run. The meter is the_ekg_reads of Episode 8. Source: 2c5e844.

S1. Heartbeat counts are identical across the five runs of every probe.
S2. (the clock, alternating.) CLAUDE: from the third tick on, the readings alternate 2162, 1141, 2162, 1141, 2162, 1141.
    The first two ticks are each a term's first reading and are recorded, not sealed.
S3. (the clock, still.) CLAUDE: from the second tick on, the device's truth reads 2162 every time, and a false reads
    1141 every time.
S4. (the clock, plain.) CLAUDE: from the third tick on, every reading is 1141: a true that is not the device's truth
    keeps no time against a false.
S5. (the quarter, cards defined beforehand, second reading.) Two rules, which exclude each other:
      AUTHOR  as Claude takes it, and the author may correct it: the meter finds the quarter. Card b reads 1021
              more than card a and card c, which read alike.
      CLAUDE  the meter does not find it: the three cards read alike, because the step is paid where the device's
              truth is named, and reading a card by its name does not name what is under it.
S6. (the quarter, cards written out in the term, second reading.) CLAUDE: here card b reads exactly 1021 more than
    card a and card c, which read alike.
    If S5 CLAUDE and S6 both hold, the meter finds the quarter only where the truth is named.

Would refute: S1 to S4 and S6, any reading other than stated. S5, each rule by the other's arrangement; any third
arrangement refutes both and is reported as found.
What it can and cannot say. It reads heartbeats of elaboration on one machine. It can show a clock that the meter
keeps and the logic does not, and whether the meter tells which card the quarter is under. Under all three cards
of S5 and S6 the logic sees a fact; under two of them a true one.
```
