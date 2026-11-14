# READINGS

Readings of the device on real hardware. These are measurements, not receipts:
the kernel checks nothing here. Each reading records what was run, where, and
what came out, so that anyone can add a row on another machine. Together they
are the readings by which we intend to find the constant.

**Protocol.** Each experiment lives in `readings/NNN-name/`. Its description,
probes and sealed prediction are committed *before* it is run; that commit's
hash is the experiment's **source**. Each reading is then committed with its raw
output, citing the source. A reading taken on another machine first checks that
its files match the source commit.

## Index of experiments

| No. | Experiment | What it asks | Source (setup commit) | Status |
|---|---|---|---|---|
| 001 | `readings/001-coupling` | heartbeats per device cell (the coupling g) and wall time per heartbeat (the dilation D) across machines | `5b8b720` | M2 and M2 Ultra read |
| 002 | `readings/002-beats` | the third clock inferred from two: the envelope extremes of the two machines' summed clocks, counted as a fringe order | `7cd707b` | M2 and M2 Ultra read |
| 003 | `readings/003-calibration` | heartbeats to seconds: the device's registered floor as one Compton time; each machine's clock against the electron's; the step's horizon | `41fd3f2` | done on both machines |

## The experiment: the coupling of the code to the implementation, and the dilation between machines

**Question.** One logical step of the device costs some amount of work in the
implementation (Lean's elaborator) and some amount of time on a given machine.
Is the work the same on every machine, so that it behaves like proper time, while
the time differs from machine to machine, like coordinate time? If so, the ratio
of times for the same work is the dilation factor between two machines.

**Meter.** Episode 8's EKG, `the_ekg_reads`. It elaborates a term and reduces it
to weak head normal form, and reports the heartbeats used, beside a blank: the
click of `FACT.Truth`, the nowtrino. Heartbeats count the elaborator's work
(allocations), not time.

**Observables.**

| Symbol | What | Unit |
|---|---|---|
| N | the nowtrino: cold cost of `FACT.Truth.click` (the blank) | heartbeats |
| H(n) | cold cost of deciding a FACT over n cells, net of the blank | heartbeats |
| C(n) | the same quantifier with every cell `True` (the control), net of the blank | heartbeats |
| g | coupling: marginal heartbeats per device cell, (H − C) per cell, divided by N | pure number |
| τ | wall time per heartbeat on the device cells, (time of H(64) − time of C(64)) / (H(64) − C(64)) | ns / heartbeat |
| D | dilation of a machine against the reference: τ / τ_ref | pure number |

**Workload.** A FACT whose truth runs over n cells of the device's own 2×2 table,
each cell checking the outer table against the middle table (the two tables of
SAME DIFFERENCE). Each cell holds two device clicks plus Boolean comparisons. The
control replaces each cell with `True`, isolating the cost of the quantifier.

**Boundary.** One fresh `lake env lean` process per reading, so every reading is
cold (Lean caches reductions after the first read). Built `Measurement.Episode12`
oleans; the probe files import it and add nothing to the repo.

### The probe

Generated for each n (device) or with the cell replaced by `True` (control):

```lean
import Measurement.Episode12
open Lean Elab Term Meta Measurement
def cellA (i : Nat) : Bool := i % 2 == 0
def cellB (i : Nat) : Bool := (i / 2) % 2 == 0
def probe : FACT :=
  { truth := ∀ i : Fin n, the_representation.outer_table (cellA i.val) (cellB i.val)
                        = the_representation.middle_table (cellA i.val) (cellB i.val)
    click := inferInstance }
elab "cold" : command => do
  Command.liftTermElabM do
    let t0 ← IO.monoNanosNow
    let (h, b) ← the_ekg_reads (← `(probe.click))
    let t1 ← IO.monoNanosNow
    logInfo m!"TIMED n=… raw={h} blank={b} net={(h:Int)-b} ns={t1-t0}"
cold
```

Run from `CARD_2/` with `lake env lean <probe>.lean`. For the timing, ten
interleaved repeats of n = 64 and n = 1, device and control.

### Sealed predictions

1. *(Sealed 14 November 2026, 16:33, before any run; sha256 a07e81c5…)* The cost
   is linear in n, and g ≈ 1. **Linear: confirmed** once the control is
   subtracted. **g ≈ 1: refuted**; g = 1.42 ± 0.02.
2. *(Sealed 14 November 2026, before the second machine was read; sha256 c7047aa8….)* The
   heartbeat counts, N, H(n), C(n) and g, are identical on every machine that
   runs the same source on the same toolchain; only τ differs. **Heartbeats:
   confirmed.** All fourteen sweep readings and all timed readings on the M2
   Ultra are identical to the M2's, to the heartbeat. **τ differs:** D = 0.956
   (0.93 to 0.98 from the interquartile ranges).

## Results on the reference machine (Apple M2)

Cold, net of the blank N = 4,152; every repeat identical to the heartbeat.

| n | H(n) | C(n) | H − C | marginal per cell | g |
|---|---|---|---|---|---|
| 1 | 8,949 | 1,567 | 7,382 | | |
| 2 | 16,018 | 2,897 | 13,121 | 5,739 | 1.38 |
| 4 | 30,549 | 5,600 | 24,949 | 5,914 | 1.42 |
| 8 | 59,392 | 11,127 | 48,265 | 5,829 | 1.40 |
| 16 | 117,925 | 22,701 | 95,224 | 5,870 | 1.41 |
| 32 | 237,452 | 47,847 | 189,605 | 5,899 | 1.42 |
| 64 | 485,900 | 105,940 | 379,960 | 5,949 | 1.43 |

Timing, ten repeats: H(64) median 18.20 ms, C(64) median 4.70 ms; the device
cells, 379,926 heartbeats, take 13.49 ms: **τ = 35.5 ns per heartbeat** (spread
32.9 to 37.6).

## Results on the M2 Ultra

Built from a copy checked file by file against `5b8b720` (build: 22 min 56 s,
14 jobs, no errors). Sweep: every N, H(n) and C(n) identical to the M2's.
Timing, ten repeats: H(64) median 17.48 ms, C(64) median 4.57 ms; the device
cells take 12.90 ms: **τ = 33.95 ns per heartbeat** (interquartile 33.8 to
34.2, tighter than the M2's 34.8 to 36.4). Against the M2: **D = 0.956**.

The two machines share a core design at nearly the same clock, so D close to 1
is expected: in the reading of the study, two frames almost at rest relative
to each other. A third machine of a different design is needed to give the
triangle size.

## Experiment 002: beats, the third clock inferred from two

**Question.** Two clocks at rates f₁ and f₂, summed, make a carrier at the mean
rate and an envelope whose extremes recur at the beat rate |f₁ − f₂|: the
moments both frames read the same phase. That is a clock neither machine
carries. Count its extremes.

**Method.** Each machine elaborates the same 400 device decisions (8 cells
each, every term new, so every reading is cold) and logs heartbeats and wall
time per step on Episode 8's meter. The heartbeat count is each clock's phase.
At equal wall time, the fringe order is F(t) = H_Ultra(t) − H_M2(t): each
whole number passed is one envelope extreme. One sample per step (about
130,000 heartbeats) cannot resolve a single fringe; F is the fringe count, as
an interferometer's counter reads it. Five runs per machine, run at the same
time. Source `7cd707b`; files in `readings/002-beats/`.

**Sealed prediction** (from 001, before any run): (a) identical heartbeat
sequences; (b) F linear, R² > 0.99; (c) F positive, the Ultra ahead; (d) one
extreme per 22 M2 heartbeats, within 13 to 52.

**Results.**

| | M2 | M2 Ultra |
|---|---|---|
| heartbeats, 400 steps | 53,977,724 | 53,977,724 |
| median time | 2,094 ms | 1,924 ms |
| τ (ns / heartbeat) | 38.80 | 35.64 |

- (a) **Confirmed.** The heartbeat sequence is identical across all ten runs
  and both machines, step by step.
- (b) **Confirmed.** F grows linearly with time, R² = 0.99916: the beat rate
  is steady along the whole run.
- (c) **Confirmed.** F is positive: the Ultra is ahead, by about 4.3 million
  extremes by the end. The sign is the direction two ratios could not give.
- (d) **Refuted.** One extreme per **11.6** M2 heartbeats (over the 25 run
  pairings: median 10.1, interquartile 9.6 to 11.1), outside 13 to 52. The beat
  rate is 2.30 MHz.

**Why (d) failed.** On this workload D = 0.918 (pairings: median 0.908,
interquartile 0.905 to 0.917), against 0.956 in 001, outside 001's range. The
dilation between the two machines depends on the workload: 002 includes the
elaboration of each new term, 001 mostly its reduction. The heartbeats per
extreme follow D exactly (1/(1/D − 1) = 11.3), so the fringe count carries the
same information as D, plus its sign and its steadiness. *Measured.*

**What it does and doesn't establish.** The third clock exists in the data:
the two machines' phases separate at a steady rate in one direction. But a
dilation that changes with the work done is not what a relative velocity does
(in relativity γ doesn't depend on what the clock is doing). Reading the
machines as frames in relative motion (*proposed*, the author's) has to
account for this: either the frame is the machine *and* the workload, or the
dilation includes a part that is not kinematic.

## Experiment 003: the calibration, heartbeats to seconds

**Rule** (sealed before any value was computed; *declared*, the author's: "compton time is rfl"):
the device's unit of work is its registered noise floor, the heartbeats of elaborating the
nowtrino's click, read at build time where calibration lives, outside the instrument. One floor
is one Compton time of the electron, t_C = ħ/(m_e c²) = ƛ_C/c. Since the count is the same on
every machine (001, 002), one heartbeat is t_C/floor on every machine. The step's rapidity is
the device's own boost (19, 2), η = ln(19 + 2√90). Source `41fd3f2`.

**The floor.** 3,016 heartbeats, read three times on each machine's own build: identical on both
(*measured*). The same click costs 4,148 to 4,152 inside Episode 12's probes, where more is in
scope; the registered floor is the device's unit, the richer environment's cost is not.

**Applied** (ƛ_C = 3.8615926744 × 10⁻¹³ m, CODATA 2022; c exact):

| | value |
|---|---|
| one floor = one Compton time | 1.2880886665 × 10⁻²¹ s |
| one heartbeat, every machine | 4.270851 × 10⁻²⁵ s |
| M2, first workload: Γ = τ / (t_C / floor) | 8.31 × 10¹⁶ (rapidity 39.652) |
| M2 Ultra, first workload | 7.95 × 10¹⁶ (rapidity 39.608) |
| M2, second workload | 9.08 × 10¹⁶ (rapidity 39.741) |
| M2 Ultra, second workload | 8.34 × 10¹⁶ (rapidity 39.656) |
| step rapidity η | 3.636893 |
| horizon distance ƛ_C/η | 1.061783 × 10⁻¹³ m = 0.274960 ƛ_C |
| acceleration c η / t_C | 8.46 × 10²⁹ m/s² |

**What the calibration corrects.** Against a common frame, the electron's clock, both machines
are dilated by about 10¹⁷, and the ratio of their clocks is a ratio of two dilations, not a
relative γ. Collinear rapidities subtract, so the relative rapidity of two machines is |ln D|:

| | ln D | relative rapidity | β |
|---|---|---|---|
| first workload | −0.0446 | 0.0446 | 0.045 |
| second workload | −0.0850 | 0.0850 | 0.085 |
| box, shared part | −0.0648 | 0.0648 | 0.065 |
| box, half the flux | ±0.0202 | | |

The earlier readings γ = 1/D (β ≈ 0.29 for the first workload, 0.35 for the box's shared part)
treated one machine's clock as proper time; the calibration shows neither is, and those values are
superseded. If the frames are not collinear, |ln D| is a lower bound on their relative rapidity
(the triangle inequality for rapidities, *standard*); a third machine tests which.

**Standing.** The floor and the τ are *measured*; the conversion is the sealed rule applied
(*computed*); that one floor is one Compton time is *declared*, the author's; reading Γ as the
machine's dilation against the electron's clock is *proposed*. No measured constant is compared.

## The study: hardware

One row per machine. The reference frame is the first row (D = 1). Add a row by
running the probes on your machine against the same source and toolchain, and
fill every column; cite the source commit so that rows are comparable. The M2
readings were taken on a working tree whose files are identical to `5b8b720`,
before it was committed; the M2 Ultra's copy was checked file by file against
`5b8b720` (20 tracked files identical).

| Exp. | Source | Machine | Chip | Cores (P + E) | Memory | macOS | Toolchain | N | g | H − C at 64 | τ (ns/heartbeat) | D |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 001 | `5b8b720` | MacBook Pro | Apple M2 | 8 (4 + 4) | 8 GB | 26.6.2 | v4.27.0-rc1 | 4,152 | 1.42 | 379,926 | 35.5 | 1 |
| 001 | `5b8b720` | Mac Studio | Apple M2 Ultra | 24 (16 + 8) | 64 GB | 26.6.2 | v4.27.0-rc1 | 4,152 | 1.42 | 379,926 | 33.95 | 0.956 |

Earlier readings, kept for comparison: a forced T = T cost 4,286.1 heartbeats on
both the M2 and the M2 Ultra (0.08% apart), with different wall times (AGENTS,
"Status, dated").

## What a row does and does not establish

- **Measured:** the heartbeat counts and wall times on that machine, for that
  source and toolchain.
- **The coupling g** is a property of the code and its implementation together.
  A different encoding of the same cell gives a different g; g is per cell, and a
  cell holds two device clicks, not yet separated.
- **The dilation D** compares clocks for the same work. That the heartbeat is the
  invariant (the proper time) and the wall time the frame's (the coordinate time)
  is a reading, *proposed*, the author's; prediction 2 tests its first half.
- Nothing here is compared with a physical constant.
