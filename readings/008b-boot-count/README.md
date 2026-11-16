# 008b — The boot count

008 read one heartbeat a turn for both routes, with a first turn of 28 for whichever route ran first and 18 for the
second, and 7 for the meter around nothing. Taking the 1 as the meter's own post, the boot readings are 7, 17 and 27:
seven plus a number of fives, none for the blank, two for the second loop, four for the first.

This experiment asks what the next loop reads, whether the post is the meter's, and whether any of it is the device's.

- `probe_boot_loops.lean`: as 008, then an empty loop, then the halving again.
- `probe_boot_blanks.lean`: five blanks in a row, then loops with a blank before each.
- `probe_boot_empty.lean`: the device imported and never touched; three empty loops.
- `probe_boot_bare.lean`: nothing imported but Lean; three empty loops.
  Output: `BLANK j hb ns`, `TURN loop kind i hb ns`.
- `run_boot.sh <CARD_2> <probe> <runs>`; `analyze_boot.py <outputs...>`.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below and this file is what the setup commit carries.

Observable: heartbeats, per turn. Boundary: `withHeartbeats` around one turn. Baseline: the blank.
What tells the readings apart: the first turn of the third loop (13, 18 or 8), and whether a loop with no device boots
the same.

Source: `16b2d0e`; the Lean it imports is unchanged since `3f797dc`. Status: read on the M2 (`raw/M2/`); see READINGS, Experiment 008b.

## The seal

```
Experiment 008b, the boot count. Sealed Mon Nov 16 10:29:44 EST 2026, before any output of these probes was read.
(Each probe was afterwards executed once to check that it compiles, with its output discarded unread.)

From 008 (source 3f797dc, read f8354ce): the meter around nothing reads 7 at its first use; every turn after a loop's
first reads 1; the first turn of the first loop reads 28 and of the second loop 18, whichever route runs.
Taking 1 as the meter's own post, the boot readings are 7, 17, 27, that is 7 + 5k with k = 0, 2, 4.

The author's reading, 16 November 2026: "boot turn might have a fencepost"; "another bootstrap of 2 there"; "you get
twice 5 back: F=T = F=T"; "that 4 is the same 4 all the way through, just go one level down."
As Claude takes it (the author may correct it): the first loop boots four fives, a frame of five for each of the four
arms; one level down is two fives; one level down again is one five.

Four probes, five runs each, one fresh process per run.
  loops:  as 008 (blank, halving, crank), then an empty loop, then the halving again; no blank between loops.
  blanks: five blanks in a row, the halving, a blank, the crank, a blank, an empty loop.
  empty:  the device imported and never touched: a blank, then three empty loops.
  bare:   nothing imported but Lean: a blank, then three empty loops.

S1. (loops) Loops 1 and 2 reproduce 008: first turns 28 and 18, later turns 1, blank 7.
S2. (loops) The first turn of loop 3. Three rules, which exclude each other:
      AUTHOR  one level down each time (fives 4, 2, 1):      reads 13
      CLAUDE  one per loop, plus one for the first (4, 2, 2): reads 18
      THIRD   two fewer each time (4, 2, 0):                  reads 8
    Loop 4's first turn is recorded and not sealed.
S3. (blanks) CLAUDE: the five blanks read 7, 1, 1, 1, 1.
S4. (blanks) CLAUDE: a blank read just before a loop does not change that loop's first turn: the three loops read
    28, 18, 18 on their first turns.
S5. (empty) CLAUDE: a loop that never touches the device boots the same: first turns 28, 18, 18, later turns 1.
S6. (bare) CLAUDE: with nothing imported but Lean the readings are the same as in S5.
    If the four is the four arms of the device, the bare probe should not boot at 28. That inference is Claude's.

Would refute: S1, any other reading; S2, each rule is refuted by a reading other than its own, and all three by a
fourth value; S3 to S6, any reading other than those stated.
All counts are expected identical across the five runs of a probe; a probe whose runs differ is reported as such.
```
