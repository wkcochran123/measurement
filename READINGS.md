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
| 003 | `readings/003-calibration` | heartbeats to seconds: the device's registered floor as one Compton time; each machine's clock against the electron's; the step's horizon | `41fd3f2` | done on both machines; the calibration withdrawn by the author, 18 November 2026 |
| 004 | `readings/004-relative-time` | the four rulers (universe level, heartbeats, time) combined into relative time through the field equations' weak-field limit | `03e888c` | M2 and M2 Ultra read |
| 005 | `readings/005-two-variations` | the two representations of the first variation, time-like (local) and space-like (the potential), and the convective term that joins them | `96a1898` | M2 and M2 Ultra read |
| 006 | `readings/006-frames` | frames as points: the M2 Ultra's performance and efficiency cores and the M2, on three workloads; the triangle's signed area; the convective term at thirty runs | `5a555d6` | read on the M2 Ultra (P and E); the M2 from 001, 002, 005 |
| 007 | `readings/007-fenceposts` | the five-block fencepost: does relative time on the ladder break at the posts 6, 11, …, 31 (seven panels of five, one post over)? | `4e5bb93` | read on the M2 Ultra; superseded by 007b |
| 007b | `readings/007b-fenceposts-both-ways` | the fencepost read both ways: do the posts beat the knot grid shifted backward as well as forward? | `a3ee8f2` | read on the M2 Ultra: refuted |
| 008 | `readings/008-two-routes` | two routes to one number: the crank (the derivative) and the halving (the sign only), each turn on the meter; do their total costs agree? | `3f797dc` | read on the M2: the heartbeat meter reads its floor for both routes; wall time separates them by 3.1 |
| 008b | `readings/008b-boot-count` | the boot count: what the first turn of a third loop reads (13, 18 or 8), whether the one heartbeat a turn is the meter's own post, and whether a loop with no device boots the same | `16b2d0e` | read on the M2: the one heartbeat a turn is the meter's own post; the boot is Lean's, not the device's; the third loop reads 18 |
| 009 | `readings/009-the-arm` | the arm: what the meter reads for the device's first order on each of the four arms | `c09cbe0` | read on the M2 |
| 009b | `readings/009b-true-from-false` | true from false: whether the meter's step belongs to a true or to the device's own truth | `d9e0ab3` | read on the M2 |
| 009c | `readings/009c-the-clock-and-the-quarter` | the clock and the quarter: eight clicks in a row, and three cards with one face | `b3ff7c3` | read on the M2 |
| 010 | `readings/010-the-value-from-nanoseconds` | the value from the nanoseconds: each count of the polynomial replaced by a timed reading of its tape over one blank; does it read slightly high? | `89b1909` | read on the M2: no real value; the author's prediction refuted as taken |
| 011 | `readings/011-the-throw` | the throw: what one application of `Quot.sound`, the device's bent card, costs on the meter, against the floor and against the step of the device's truth | `25dc6e3` | read on the M2: 23,752 heartbeats, 5.64 blanks; all three sealed rules refuted |
| 012 | `readings/012-the-enumeration` | the enumeration: rises 1 to 4 by levels 0 to 6 on the meter; does the floor under the reading change with the rise? | `c21c5c9` | read on the M2: the slope scales with the rise and the floor does not; all sealed rules confirmed |

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
   *Erratum, 19 November 2026.* The sealed file says what would refute the second half: "g far from 1 (outside
   0.5..2)". The reading, 1.42, is inside that range. By the seal's own criterion the second half is **not refuted**.
   What is measured is that g is 1.42 and not 1. The verdict above was written stricter than the seal and is corrected
   here, not erased.
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

**Withdrawn, 18 November 2026.** The author withdrew the rule this experiment applies, that one floor is one Compton
time of the electron. The section below is kept as it was read and computed, because it was sealed and run; nothing in
it is asserted any longer. The floor, 3,016 heartbeats on both machines, and each machine's τ are measurements and
stand. Every value computed from the rule (seconds per heartbeat, Γ, the rapidities against the electron's clock, the
horizon distance, the acceleration) is withdrawn. The machines' relative rapidity |ln D| does not depend on which common
frame is taken and stands as a reading under the assumption that there is one.

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

## Experiment 004: relative time from the four rulers

**Question** (the author's four rulers): universe levels, heartbeats and time, combined to compute
relative time through the Einstein field equations. In the weak field a clock at potential Φ runs at
1 + Φ/c² (*standard*), and the potential is sourced by the energy density. On a line of universe
levels the potential is a double sum of the density, whose second difference is the density: now a
kernel receipt, `the_second_difference_of_the_potential_is_the_density`, with
`a_nonnegative_density_bends_the_potential_up` and `the_potentials_superpose` (Episode 12,
propext and Quot.sound). Source `03e888c`.

**Method.** At each level k = 1…36 the typeset ladder is searched for rung k on a place one universe
lower, on Episode 8's meter, with wall time. H_k = heartbeats (beat + blank), τ_k = t_k / H_k,
relative time R_k = τ_k / τ_2 (level 1, the cold start, excluded), density ρ_k = H_k, potential Φ_k
the double sum of ρ below k. Five runs per machine, both machines at once.

**Against the seal:**

| | prediction | result |
|---|---|---|
| (a) | H_k identical across runs and machines | **confirmed**: all 36 levels, all ten runs, from 16,026 to 626,925 heartbeats |
| (b) | D_k = τ_k(Ultra)/τ_k(M2) constant within the M2's run-to-run spread (0.051); no trend in Φ | **refuted** as sealed: D_k spans 0.887 to 0.983 (spread 0.10, median 0.954); **no trend**: R² = 0.11 |
| (c) | ln R_k linear in Φ_k, R² > 0.9; the two slopes within 20% | **mixed**: M2 R² = 0.859 (fails), Ultra 0.905 (holds); slopes 3.94 × 10⁻⁹ and 3.67 × 10⁻⁹ per heartbeat², 7% apart (holds) |

Relative time rises up the ladder on both machines: τ goes from 33.5 to 40.0 ns per heartbeat on the
M2, and from 31.5 to 37.2 on the Ultra, between levels 2 and 36. The two machines' ratio has no trend
with height, so the rise is shared. Its scatter is the M2's clock (one level, 12, reads 10% slow on
the M2 alone).

**After the fact, not sealed:** ln R_k tracks the local density H_k better than the potential Φ_k.
From level 5 on, R² against H_k is 0.955 (M2) and 0.991 (Ultra), against Φ_k 0.886 and 0.932,
against the field (single sum) 0.929 and 0.970. A clock that reads the work at its own level
rather than the potential below it is what 002's workload dependence suggested: a medium, not a
field. That is a candidate for a sealed prediction in the next experiment, not a result here.

**Standing.** The counts and times are *measured*; the potential is *computed* from the counts by the
receipt; that heartbeats per level are an energy density and universe levels a height, and that
the rise is gravitational time dilation, is *proposed*, the author's. The weak-field relations are
*standard*.

## Experiment 005: two first variations, and the convective term

**Question** (the author's): the first variation has two representations, time-like (along the clock
at a place: the local rate) and space-like (across places at one time: the difference between levels,
summed into a potential). A fluid law joins them in the material derivative, the time-like variation
plus the convective term u·∇u. **Receipts** (Episode 12, propext and Quot.sound): `a_boost_keeps_the_kind`,
`time_like_stays_time_like`, `space_like_stays_space_like` (the kind of a variation is the same in every
frame); `one_variation_two_representations` (along a step one tick and one level, either order gives the
whole, and the orders meet in the mixed difference); `the_convective_term` (2ud = (u+d)² − u² − d²).
Source `96a1898`.

**Method.** A new workload, so 004's data could not pass it: step k = 0…47 decides k + 1 cells, every
term new. H_k = heartbeats, τ_k = t_k / H_k, u_k = 1/τ_k, ln R_k = ln(τ_k / τ_4), steps 0–3 warm-up.
Five runs per machine, at once.

**Against the seal:**

| | prediction | result |
|---|---|---|
| (a) | H_k identical across runs and machines | **confirmed**, all 48 steps, all ten runs |
| (b) | the time-like representation fits better than the space-like | **confirmed**: R² local 0.928 vs potential 0.826 (M2); 0.978 vs 0.846 (Ultra) |
| (c) | the local fit's residual correlates with u_k(u_{k+1} − u_{k−1}), same sign, \|r\| ≥ 0.3 | **refuted**: same sign, but r = +0.044 (M2) and +0.040 (Ultra) |

τ rises from 32.6 to 39.3 ns per heartbeat on the M2 and from 32.3 to 37.0 on the Ultra over the 48
steps. The time-like reading, a clock that follows the work at its own step, now holds as a sealed
prediction on a second workload, not only after the fact. The convective term does not show at this
resolution: whatever joins the two representations is below the clock's noise, or is not of the form
u·Δu, on these readings.

**Standing.** Counts and times *measured*; the fits *computed*; that the local and integrated fits are
the time-like and space-like first variations, and that a fluid law joins them, *proposed*, the author's.

## Experiment 006: frames as points

**Why.** A triangle of single clock ratios cannot fail: ln(τ₁/τ₂) + ln(τ₂/τ₃) = ln(τ₁/τ₃) always, zero
circulation again. So each frame is read on several workloads and becomes a point, (ln τ_W1, ln τ_W3),
and three frames have a signed area, the quantity Episode 12's `the_orientation` reads. Frames: the M2
Ultra on its performance cores (P), on its efficiency cores (E, `taskpolicy -c background`, a different
core design), and the M2 (its readings of the same probes in 001, 002, 005). Workloads: W1 = 001's 64
cells net of control, W2 = 002's 400 steps, W3 = 005's growing steps. Source `5a555d6`. Run on the Ultra
alone, one frame after the other.

**Results:**

| frame | τ, W1 | τ, W2 | τ, W3 (ns per heartbeat) |
|---|---|---|---|
| Ultra P | 33.74 | 35.55 | 35.33 |
| Ultra E | 231.95 | 244.61 | 242.18 |
| M2 | 35.50 | 39.28 | 37.10 |

| | prediction | result |
|---|---|---|
| (a) | every count identical across frames | **confirmed**: W1 494,198 (beat + blank), W2 53,977,724, W3 12,149,451 on all three frames |
| (b) | E a distinct frame, beyond ten spreads of P | **confirmed**: ln(τ_E/τ_P) = 1.928, 1.929, 1.925 on the three workloads, against ten spreads of 0.32, 0.08, 0.33 |
| (c) | the frames' signed area excludes zero | **refuted**: −0.0034, 95% bootstrap interval −0.063 to +0.140: collinear within the noise, so no orientation from these three |
| (d) | the convective term at thirty runs, r ≥ +0.3 | **refuted**: r = +0.006 |

**What it shows.**
- **The efficiency cores dilate the clock by one factor for every workload**: 6.875, 6.881 and 6.855,
  within 0.4% of each other. On one machine, a change of frame multiplies the time of every kind of
  work alike, as a Lorentz factor does: γ does not depend on what the clock is doing.
- **The workload dependence sits in the M2's row.** The 3 × 3 interaction (double-centered ln τ) is
  +0.005, −0.012, +0.007 for Ultra P; +0.006, −0.010, +0.004 for Ultra E; and −0.011, +0.022, −0.011 for
  the M2, its largest entry on W2, the beats run made with both machines working at once. The flux the
  box attributed to the work (002, the box, the reading of a medium) is, on this evidence, mostly the
  M2's: a noisy laptop, not a property of the work. On the clean machine the frames differ by a pure
  dilation.
- **No orientation yet.** Because the clean frames differ by one factor, their points lie on a line,
  and the triangle has no area to read. A pointer needs frames that differ by more than a factor.
- **No convective term.** At thirty runs on the steadiest clock, the local fit's residual is
  uncorrelated with u·Δu (r = +0.006).

**A note on the run.** On macOS `seq 1 0` counts down (1, then 0), so the convective pass also ran two
repeats each of W1 and W2; they are in the raw file and unused. The first analysis took a W2 run as a
W3 run and failed; the fix, reading only W3 runs, is in the committed analysis. The predictions are
unchanged.

**Standing.** Counts and times *measured*; the fits, the interval and the interaction *computed*; that a
workload-independent dilation is a Lorentz factor, and that frames as points give the knower's
orientation, *proposed*.

## Experiment 007: the five-block fencepost

**Question** (the author's reading of 004's mixed fit: "5 block fencepost"). The 36 levels are seven
panels of five with one post over, 36 = 7·5 + 1: the thirty-five lifts and the fencepost. Read panel
by panel, relative time should break at the posts. Sealed before any run, and 004's data were not
refitted. Source `4e5bb93`; ten runs of 004's ladder probe on the M2 Ultra's performance cores.

| shift | interior knots | residual (RSS) |
|---|---|---|
| **0 (the posts)** | 6, 11, 16, 21, 26, 31 | **4.63 × 10⁻³** |
| 1 | 7, 12, …, 32 | 5.69 × 10⁻³ |
| 2 | 8, 13, …, 33 | 6.71 × 10⁻³ |
| 3 | 9, 14, …, 34 | 7.36 × 10⁻³ |
| 4 | 10, 15, …, 35 | 7.75 × 10⁻³ |

- (a) **confirmed**: the counts are identical across the ten runs and equal to 004's at every level.
- (b) **confirmed**: the spline with knots on the posts has the smallest residual, 19% below the best
  shifted grid; R² = 0.985 with six knots, against 0.905 for the potential in 004.

**Caveat.** The residual rises steadily with the shift, so a reading in which earlier breaks simply fit
better is not excluded by this test. Grids shifted the other way (5, 10, …, 30; 4, 9, …, 29) would
separate the posts from that trend; that is the next seal.

**Standing.** *Measured*: counts and times; *computed*: the fits. *Proposed*, the author's: the
ladder's relative time is read in panels of five between fenceposts, the Sobolev-exact panels of the
spline.

## Experiment 007b: the fencepost read both ways

**Why.** 007's residual rose steadily with the forward shift, so a trend toward earlier breaks was not
excluded. 007b adds the backward shifts. Sealed before any run; source `a3ee8f2`; ten fresh runs of
004's ladder probe on the M2 Ultra.

| shift | knots | residual (RSS) |
|---|---|---|
| −3 | 3, 8, …, 28 | **4.62 × 10⁻⁴** |
| −2 | 4, 9, …, 29 | 1.83 × 10⁻³ |
| −1 | 5, 10, …, 30 | 3.45 × 10⁻³ |
| 0 (the posts) | 6, 11, …, 31 | 4.96 × 10⁻³ |
| 1 | 7, 12, …, 32 | 6.10 × 10⁻³ |
| 2 | 8, 13, …, 33 | 7.12 × 10⁻³ |
| 3 | 9, 14, …, 34 | 7.59 × 10⁻³ |
| 4 | 10, 15, …, 35 | 8.00 × 10⁻³ |

- (a) **confirmed**: counts identical across the ten runs and equal to 004's.
- (b) **refuted**: the residual falls steadily as the knots move earlier; shift −3 fits ten times better
  than the posts. 007's result was the trend it could not exclude.

**What it shows.** Relative time dips over the first levels before it rises (τ falls from level 2 to
about level 5 on both machines in 004), and a knot near level 3 takes up that dip. The five-level panels
between posts are not what the clock shows; the shared rise up the ladder stands, its shape not settled.
Shift −4 was left out by the seal: its first knot sits on level 2, where it is collinear with the line.

## Experiment 008: two routes to one number

The ladder read down (Episode 12, `THE LADDER, READ DOWN`) says two versions of the computation agree at every rung
and that what separates them is conserved and can be measured. The device has two routes to its number that share no
step: the crank, which uses the derivative, and the halving, which uses only the sign of the residual. That they meet
is a receipt (`the_reading_with_its_receipt`, minted as `THE_CH_VERSION_IS_THE_NON_CH_VERSION`).

**What is measured.** Heartbeats and wall time for every turn of each route, one turn per cell of the strip, in one
fresh process; once with the halving first and once with the crank first; five runs of each.

**The seal** (`readings/008-two-routes/SEALED_PREDICTION.txt`). (a) Counts identical across runs and orders. (b) Both
routes end on the build's own bracket and point. Then two accounts that exclude each other: (c) the totals agree
within one per cent (conservation read strictly; the operational reading is proposed and the author may replace it
before the run), or (d3) they differ by more. Also (d1) the halving's heartbeats per turn are flat, and (d2) its wall
time per turn grows.

**Result on the M2** (MacBook Pro, Apple M2, 8 cores, 8 GB, macOS 26.6.2, Lean v4.27.0-rc1; source `3f797dc`; raw
output and analysis in `readings/008-two-routes/raw/M2/`). Five runs of each probe.

| | Halving | Crank |
|---|---|---|
| Heartbeats, turn 0, when run first | 28 | 28 |
| Heartbeats, turn 0, when run second | 18 | 18 |
| Heartbeats, each of turns 1 to 105 | 1 | 1 |
| Total heartbeats, run first / run second | 133 / 123 | 133 / 123 |
| Wall time, turns 1 to 105, median (ms) | 0.29 | 0.90 |
| Wall time per turn, early / late (µs) | 1.5 / 3.1 | 8.9 / 8.3 |

The meter around nothing reads 7. Every count is identical in all ten runs.

Against the seal:

- (a) Identical across runs: confirmed. Independent of order: **refuted**. The first turn reads 28 for whichever route
  runs first and 18 for whichever runs second.
- (b) Both routes end on the build's own bracket and point: confirmed.
- (c) Account A as sealed, 133 against 123, 7.5 per cent apart: **refuted as sealed**. (d3) Account B: confirmed as
  sealed.
- (d1) The halving's heartbeats are flat: confirmed, trivially. (d2) Its wall time per turn grows: confirmed, from about
  1.5 to 3.1 microseconds.

What the reading shows is narrower than either account. The difference of ten heartbeats belongs to the position in the
process and not to the route: at the same position the two routes have exactly equal totals. And they are equal because
the meter reads its floor, one heartbeat a turn, for both. On this workload the heartbeat count does not see the
arithmetic of either route. (008b shows the one is the meter's own post: each turn cost no heartbeats.) So the reading neither supports nor refutes conservation of cost between the routes; it
shows this meter cannot weigh them. The seal's choice of the first run of one probe as the comparison was a flaw in the
seal, and the second probe is what exposed it.

**Correction, 16 November 2026 (later).** "This meter cannot weigh them" is the wrong conclusion. A heartbeat is the
count of small memory allocations in a thread (the Lean reference, `IO.getNumHeartbeats`); the toolchain only ever
increments it, on an allocation, and never decrements it when memory is freed. It is a one-way count of marks written.
The probes ran each route in place, overwriting its own state, so the routes wrote nothing and the meter read nothing.
The reading shows that a computation that keeps no record costs nothing on this meter. It does not show that the meter
cannot weigh the routes: the device weighs them by their ledgers, which the build writes and the kernel checks
(`frechet_walk`). The ledgers are one length, 107 states each (`the_two_ledgers_are_one_length`); the halving writes a
new state at every turn and the crank writes seven and then repeats (`the_halving_writes_a_new_state_every_turn`,
`the_crank_writes_seven_and_then_repeats`).

Wall time does separate the routes. The crank takes 3.1 times as long as the halving, in either order (3.07 and 3.10).
The crank's time per turn is level across all 106 turns, including the turns after it has halted; the halving's grows
as its numbers grow.

**Status.** Read on the M2. Not read on the M2 Ultra.

## Experiment 008b: the boot count

008 left three boot readings: 7 for the meter around nothing, 28 for the first turn of the first loop and 18 for the
first turn of the second, with 1 on every other turn. This experiment asks what a third loop reads, whether the 1 is
the meter's own, and whether any of it belongs to the device.

**Result on the M2** (source `16b2d0e`; the Lean it imports is unchanged since `3f797dc`; raw output and analysis in
`readings/008b-boot-count/raw/M2/`). Four probes, five runs each; every count identical across the five runs.

| Probe | Blanks | First turn of each loop, in order | Later turns |
|---|---|---|---|
| loops: halving, crank, empty, halving again | 7 | 28, 18, 18, 1 | 1 |
| blanks: five blanks, then halving, blank, crank, blank, empty | 7, 1, 1, 1, 1, then 1, 1 | 28, 18, 18 | 1 |
| empty: the device imported, never touched; three empty loops | 7 | 28, 1, 1 | 1 |
| bare: nothing imported but Lean; three empty loops | 7 | 28, 1, 1 | 1 |

Against the seal:

- S1, loops 1 and 2 reproduce 008: confirmed.
- S2, the first turn of the third loop: it reads 18. The author's reading as taken (13, fives 4, 2, 1) is **refuted**;
  the third rule (8) is refuted; the value sealed under Claude's rule is confirmed. The rule itself (one per loop, plus
  one for the first) is wrong all the same: the fourth loop, the halving run again, reads 1, and S5 fails.
- S3, the blanks read 7, 1, 1, 1, 1: confirmed.
- S4, a blank before a loop changes nothing: confirmed.
- S5, an empty loop boots 28, 18, 18: **refuted**. It reads 28, 1, 1.
- S6, the bare probe reads as sealed in S5: **refuted** as sealed. It reads exactly what the empty probe reads.

What the readings show:

1. The one heartbeat a turn is the meter's own post. A warmed meter around nothing reads 1. So in 008 each turn of
   either route cost no heartbeats at all. The author's "boot turn might have a fencepost" is right in this respect.
   (Corrected, later the same day: not "the meter does not see the routes". The routes, run in place, wrote no marks,
   and the meter counts marks written. See the correction under 008.)
2. The boot is paid once for each new body of code, not once for each loop. The first loop in the process reads 28. A
   later loop reads 18 the first time its body is one not yet run (the crank after the halving, the empty loop after
   both) and 1 when its body has run before (the halving again; the second and third empty loops).
3. None of it is the device's. With nothing imported but Lean the readings are 7 and 28, the same as with the device.
   The fives in 7, 17, 27 are the elaborator's.

These offsets, a post of 1 and a boot of at most 28, are negligible against the thousands of heartbeats read in 001 to
007, which measured elaboration and not compiled arithmetic. They are the whole of what 008 read.

**Status.** Read on the M2. Not read on the M2 Ultra.

## Experiment 009: the arm

**Setup:** `c09cbe0` (`readings/009-the-arm/`). **Source:** `2c5e844`; the probes import Episode 8 and nothing
later. **Read:** Apple M2, 17 November 2026, five runs per probe, one fresh process per run; `raw/M2/`.
All fifteen probes compiled as sealed; no probe was repaired.

**What was read.** The device's own meter, `the_ekg_reads`, on two of the device's own orders, arm by arm:
`Number.le` on the four arms of two one-cell numbers whose facts are the true and the false, and
`Abstraction.le` on the four pairs of compile and execute. Each read gives the heartbeats of the arm and the
blank drawn with it.

| Arm | First reading in a fresh process | Second reading | Blank (first, second) |
|---|---|---|---|
| `Number.le` T,T | 20,111 | 17,712 | 4,148, 3,735 |
| `Number.le` T,F | 18,866 | 16,691 | 4,148, 3,735 |
| `Number.le` F,T | 18,867 | 16,691 | 4,148, 3,735 |
| `Number.le` F,F | 17,858 | 15,670 | 4,148, 3,735 |
| `Abstraction.le` C,C | 14,679 | 13,058 | 4,148, 3,735 |
| `Abstraction.le` C,E | 14,706 | 13,058 | 4,148, 3,735 |
| `Abstraction.le` E,C | 14,704 | 13,058 | 4,148, 3,735 |
| `Abstraction.le` E,E | 14,681 | 13,058 | 4,148, 3,735 |

The meter around nothing read 7 in every process.

**Against the seal.**

- **S1, confirmed.** Every probe's five runs are identical.
- **S2, all four rules refuted.** The second readings of `Number.le` are three values, not one, two or four:
  F,F reads 15,670; T,F and F,T both read 16,691; T,T reads 17,712. The steps are equal: 1,021 and 1,021.
  AUTHOR (as Claude rendered it) is refuted: T,F is not the least, and T,F and F,T read alike. CLAUDE is refuted:
  T,T is the greatest, but the other three do not read alike. PAIRS is refuted: the two sames differ. NULL is
  refuted. The arrangement found is none of the four and is reported as found.
- **S3, refuted.** The first reading exceeds the second by 2,399 (T,T), 2,175 (T,F), 2,176 (F,T) and 2,188 (F,F):
  not one amount. The order of the arms is the same on first readings as on second.
- **S4, confirmed.** In all three order probes each arm's second-pass reading is its single-arm second reading.
- **S5, CLAUDE refuted; NULL holds.** All four pairs of `Abstraction.le` read 13,058 on the second reading. Their
  first readings in a fresh process differ by at most 27.
- **S6, confirmed.** No arm reads the blank.

**What it says.** On this meter the reading of an arm of `Number.le` is 15,670 and 1,021 for each coin that is the
true: none, one, two. The two arms with one true coin, which the order itself sends to opposite verdicts, are not
told apart. So the meter separates three things by two equal steps, and it does so by the coins, not by the arm.
`Abstraction.le` is not told apart at all once the process is warm.

**What it does not say.** The true and the false are different terms here (`FACT.Truth` of Episode 1, and a false
fact defined in the probe), so the step of 1,021 may be the cost of the true as a term and not of anything the order
does with it; the experiment cannot separate the two. It does not say which arm is a, b or c of the author's
formula: no single arm is set apart. One machine, one toolchain.

**Status.** Read on the M2. Not read on the M2 Ultra.

## Experiment 009b: true from false

**Setup:** `d9e0ab3` (`readings/009b-true-from-false/`). **Source:** `2c5e844`. **Read:** Apple M2, 17 November
2026, five runs per probe, one fresh process per run; `raw/M2/`. All twenty probes compiled as sealed.

**What was read.** Four facts, a true and a false built each of two ways. T0 is the device's own truth, `FACT.Truth`
of Episode 1, whose statement is the boolean true. F1 is a false built the same way. F0 is the false of 009, whose
statement is `False`. T1 is a true built the same way, whose statement is `True`. The meter read the click of each
alone, and `Number.le` on each of the sixteen ordered pairs.

Second readings, in heartbeats. The click alone: T0 2,162; T1 1,141; F0 1,141; F1 1,141. The sixteen arms:

| first \ second | T0 | T1 | F0 | F1 |
|---|---|---|---|---|
| **T0** | 17,712 | 16,691 | 16,691 | 16,691 |
| **T1** | 16,691 | 15,670 | 15,670 | 15,670 |
| **F0** | 16,691 | 15,670 | 15,670 | 15,670 |
| **F1** | 16,691 | 15,670 | 15,670 | 15,670 |

**Against the seal.**

- **S1, confirmed.** Every probe's five runs are identical.
- **S2, confirmed.** The four arms of 009 read as they did: 17,712, 16,691, 16,691, 15,670.
- **S3 (additive), confirmed.** Every arm reads 15,670 plus one number for each of its two facts. The number is 1,021
  for T0 and nothing for T1, F0 and F1.
- **S4, both rules refuted.** AUTHOR: a true's number is not greater than a false's, since T1 reads as the falses do.
  CLAUDE: the facts with a boolean statement do not read more, since F1 reads as F0 does. Found: one fact of the
  four carries the step, the device's own truth.
- **S5, both rules refuted,** the same way: the click of T0 reads 2,162 and the other three read 1,141.

**What it says.** The step of 1,021 in 009 belongs neither to truth nor to the way the statement is written. It
belongs to `FACT.Truth`. A fact that is true and is not the device's truth reads as a false reads. So the meter does
not tell true from false; it tells the device's one truth from every other fact, true or false.

**What it does not say.** Why. `FACT.Truth` differs from the other three in being defined in Episode 1 and named
through its namespace, where the others are defined in the probe and named plainly; the experiment does not
separate those. One machine, one toolchain, four facts.

**Status.** Read on the M2. Not read on the M2 Ultra.

## Experiment 009c: the clock and the quarter

**Setup:** `b3ff7c3` (`readings/009c-the-clock-and-the-quarter/`). **Source:** `2c5e844`. **Read:** Apple M2,
17 November 2026, five runs per probe, one fresh process per run; `raw/M2/`. All ten probes compiled as sealed.

**The clock.** Eight clicks in a row in one process, in heartbeats:

| Probe | Ticks 0 to 7 |
|---|---|
| the device's truth, a false, turn about | 2,189, 1,339, 2,162, 1,142, 2,162, 1,142, 2,162, 1,142 |
| the device's truth every time | 2,189, 2,162, 2,162, 2,162, 2,162, 2,162, 2,162, 2,162 |
| a false every time | 1,364, 1,141, 1,141, 1,141, 1,141, 1,141, 1,141, 1,141 |
| a true that is not the device's truth, a false, turn about | 1,365, 1,339, 1,141, 1,142, 1,141, 1,142, 1,141, 1,142 |

**The quarter.** Three cards with one face; under card a the quarter stands on a false, under card b on the device's
truth, under card c on a true that is not the device's truth. Second readings:

| | card a | card b | card c |
|---|---|---|---|
| the card defined beforehand and read by its name | 2,080 | 2,080 | 2,080 |
| the card written out in the term that is read | 8,593 | 9,589 | 8,581 |

**Against the seal.**

- **S1, confirmed.** Every probe's five runs are identical.
- **S2, refuted by one heartbeat.** The alternating clock reads 2,162 on the truth as sealed, and 1,142 on the false,
  where 1,141 was sealed. It alternates from the third tick on.
- **S3, confirmed.** Still, the truth reads 2,162 every time and the false 1,141 every time, from the second tick.
- **S4, refuted.** Sealed: every reading 1,141, no clock. Read: 1,141 and 1,142 turn about. A true that is not the
  device's truth does keep time against a false, by one heartbeat.
- **S5, CLAUDE holds; AUTHOR (as Claude rendered it) refuted.** Read by name, the three cards read alike, 2,080.
- **S6, refuted as stated.** Written out, card b reads more than the others, but by 996 and 1,008, not by 1,021, and
  cards a and c do not read alike: they are 12 apart.

**What it says.** The meter keeps a clock that the logic does not. Against a false, the device's truth ticks 2,162
and 1,142. Any change of term costs one heartbeat: the false reads 1,141 when it is repeated and 1,142 when it
follows something else, and that one heartbeat is the whole of the clock between a plain true and a false. And the
meter does not find the quarter under a card that is read by its name. It reads about a thousand more for the card
with the device's truth under it only when what is under the card is written in the term that is read.

**What it does not say.** Why the step is paid where the truth is named; why the written-out step is 996 or 1,008
and not 1,021; or anything about another machine or toolchain.

**Status.** Read on the M2. Not read on the M2 Ultra.

## Experiment 010: the value from the nanoseconds

**Setup:** `89b1909` (`readings/010-the-value-from-nanoseconds/`). **Source:** `10a1184`. **Read:** Apple M2,
17 November 2026, ten interleaved runs, one fresh process per reading; `raw/M2/readings.out`. All eight probes compiled
as sealed.

**The author's statement:** "the experiment is to use the nanoseconds to compute the value using the polynomial
directly. that should read _slightly_ high." Taken, with "the length is one blank", as: replace each count the
polynomial uses by the time to read its tape over the time to read one blank.

**Read.** Each tape with every cell clicked once, on the EKG's two lines:

| Tape | Cells | Heartbeats (all ten runs) | Nanoseconds, median (least to greatest) |
|---|---|---|---|
| no tape | 0 | 18,711 | 2,814,020 (2,202,250 to 7,077,250) |
| one blank | 1 | 23,215 | 2,447,375 (2,230,000 to 10,711,666) |
| the basis' reading | 2 | 22,442 | 2,793,188 (2,385,667 to 6,033,791) |
| Gauss's | 5 | 29,636 | 5,604,396 (2,669,000 to 18,284,375) |
| the coefficient tape | 13 | 84,018 | 5,050,750 (4,899,750 to 24,981,125) |
| the memory tape | 18 | 93,908 | 5,358,875 (5,094,917 to 24,326,625) |
| the epsilon tape | 18 | 93,949 | 5,519,104 (5,201,708 to 39,732,375) |
| the description | 106 | 1,085,049 | 40,203,021 (37,892,500 to 47,293,166) |

**The value, by each rule** (with the counts the formula gives 137.011291, discriminant 360):

| Rule | e, g, a, b, m | Discriminant | Value |
|---|---|---|---|
| A, nanoseconds over one blank | 2.255, 2.290, 2.064, 1.141, 2.190 | −11.8 | none |
| B, heartbeats over one blank | 4.047, 1.277, 3.619, 0.967, 4.045 | −43.3 | none |
| C, nanoseconds net of no tape (recorded) | −7.38, −7.61, −6.10, 0.06, −6.94 | −169 | none |
| D, heartbeats net of no tape (recorded) | 16.70, 2.43, 14.50, 0.83, 16.70 | −777 | none |

Rule A run by run: a value in two runs of ten (129.922 and 9.578), none in the other eight.

**Against the seal.**

- S1, heartbeats identical across runs: **confirmed**, all eight probes.
- S2, rule A. AUTHOR (slightly high, within one part in a hundred above): **refuted, as taken**. CLAUDE (no value, or
  more than one part in a hundred away): **confirmed**; the discriminant is negative.
- S3, rule B: **confirmed**; the discriminant is negative.
- S4, the heartbeats are not in the ratio of the cells: **confirmed**.

**What it says.** A clock in the reader's seat does not return the counts, and the polynomial is not forgiving of
that: it has a real root only while the readings stay within about fifteen parts in a hundred of the counts together.
Three things keep the readings away. The one blank is dear: one cell of the device's truth costs 4,504 heartbeats
over no tape, and two cells of the basis' reading cost less than that one. The cost per cell is not one number: over
no tape it is about 1,870 a cell for the basis' reading, 2,190 for Gauss's, 5,020 for the coefficient tape, 4,180 for
the memory tape and 10,060 for the description. And at these sizes the clock is not reading the tape: no tape took
longer, in the median, than one blank, and the spread of a single probe is several times the difference between
probes. Rule D, the heartbeats net of no tape, is the nearest to the counts on the long tapes (16.7, 14.5, 16.7
against 18, 13, 18) and the farthest on the short ones.

**After the run, the author's.** "see, you can distinguish a number. qed", and, of the prediction: "'slightly high'
is the fact that the actual time cannot be measured, only bounded from below." Both were said after the readings were
in, and neither is the sealed prediction, which was about the value and was taken wrongly; they are *declared*. What
the readings show of the second: in ten runs of each tape, the readings other than the least lay above it, on one
side.

| Tape | Least, ns | Median over least | Greatest over least |
|---|---|---|---|
| no tape | 2,202,250 | 1.28 | 3.2 |
| one blank | 2,230,000 | 1.10 | 4.8 |
| the basis' reading | 2,385,667 | 1.17 | 2.5 |
| Gauss's | 2,669,000 | 2.10 | 6.9 |
| the coefficient tape | 4,899,750 | 1.03 | 5.1 |
| the memory tape | 5,094,917 | 1.05 | 4.8 |
| the epsilon tape | 5,201,708 | 1.06 | 7.6 |
| the description | 37,892,500 | 1.06 | 1.25 |

With the least of each tape in place of the median, rule A still gives no value (*computed*; recorded, not sealed).
The demonstration is now also in line: `Episode13.lean` reads the five tapes and one blank at every elaboration and
prints the value on the count, on the heartbeats and on the clock.

**Standing.** The heartbeats and nanoseconds are *measured*, on one machine. The values are *computed* by the sealed
rules. That the experiment the author meant is the one run here is Claude's reading, and the author may correct it:
the unit, the workload that reads a tape, and which counts are replaced were all chosen in the setup. A different
choice of any of them is a different experiment and needs its own seal.

## Experiment 011: the throw

**Note, 18 November 2026.** The sentence this experiment took up, that the Compton time is the time it takes to throw a
bent card, went with the Compton identification when the author withdrew it. The readings below stand as what one
application of `Quot.sound` and of `propext` cost on the meter. They are no longer read against a physical time.

**Setup:** `25dc6e3` (`readings/011-the-throw/`). **Source:** `cc347cb`. **Read:** Apple M2, 17 November 2026, five runs
per probe, one fresh process per run; `raw/M2/`. All six probes compiled as sealed.

**The author's statement:** "compton time is the time it takes to throw a bent card." With one floor as one Compton
time (003) and `Quot.sound` as the device's bent card, taken as: one application of `Quot.sound` costs, on the meter,
one floor; or, the other way it can be taken, the step of 1,021 that belongs to the device's truth.

**Read**, in heartbeats, each term read twice in one process beside its blank:

| Probe | First reading (blank) | Second reading (blank) |
|---|---|---|
| `Quot.sound` applied once | 53,771 (4,626) | 50,707 (4,213) |
| the same statement by `rfl` | 27,846 (4,626) | 26,955 (4,213) |
| `propext` applied once | 17,342 (4,626) | 17,302 (4,213) |
| the same statement by `rfl` | 11,535 (4,626) | 11,529 (4,213) |
| the device's truth, as a term | 4,213 (4,626) | 4,202 (4,213) |
| Episode 8's own throw, by name | 3,101 (4,630) | 2,255 (4,213) |

**The throws,** on the second reading, each net of its control:

| | Heartbeats | In blanks (4,213) | In steps (1,021) |
|---|---|---|---|
| `Quot.sound` | 23,752 | 5.64 | 23.3 |
| `propext` | 5,773 | 1.37 | 5.65 |

**Against the seal.**

- S1, heartbeats identical across runs: **confirmed**, all six probes.
- S2, the throw of the bent card. AUTHOR-FLOOR (within one part in ten of the blank): **refuted, as taken**; it is 5.64
  blanks. AUTHOR-STEP (1,021 to within 50): **refuted, as taken**. CLAUDE (under 500): **refuted**; it is 23,752. None
  of the three; reported as found.
- S3, propext's throw under 500 and within 300 of the sound's: **refuted** on both counts; it is 5,773, a quarter of
  the sound's.
- S4, the throw read by its name costs less than the throw written out: **confirmed**, 2,255 against 50,707.

**What it says.** Throwing the bent card is not free and is not one floor. Written out, one application of `Quot.sound`
costs the meter 23,752 heartbeats over the same statement proved with nothing thrown, between five and six times what
the device's truth costs to click beside it; `propext` costs 5,773, about a quarter as much. So the meter does tell the
two axioms apart, by a factor of 4.11, which Claude's rule said it would not. Read by its name the throw costs almost
nothing, as 009c found of cards: the cost is paid where the throw is written. Two ratios are recorded and not
explained: the sound's throw over propext's is 4.114, and the blank over the step is 4.126; and so the sound's throw
in blanks, 5.64, is nearly propext's throw in steps, 5.65.

**Standing.** The heartbeats are *measured*, on one machine. That a throw is `Quot.sound` applied once to a statement of
Episode 8's box, read net of the same statement by `rfl`, is Claude's reading of the author's sentence, and the author
may correct it: the statement thrown, the control, and which reading is taken were chosen in the setup. The author's
sentence stands as *declared*; as taken here it is not borne out.

## Experiment 012: the enumeration

**Setup:** `c21c5c9` (`readings/012-the-enumeration/`). **Source:** `101f871`. **Read:** Apple M2, 18 November 2026, three
runs, one fresh process per reading; `raw/M2/readings.out`. All twenty-eight probes compiled as sealed.

**The author's statements:** "the meter's floor is also known, the input is finite, the run is finite, the tape is
finite. simple lba enumeration will provide the scaling." And: "\hbar = 1 all constants are 1 blank in size".

**Read**, in heartbeats; the blank beside every reading was 4,626. Each tape has rise × level(level+1)/2 cells of the
device's truth, every cell clicked once:

| Level | Rise 1 | Rise 2 | Rise 3 | Rise 4 |
|---|---|---|---|---|
| 0 | 21,259 | 21,259 | 21,259 | 21,259 |
| 1 | 24,055 | 25,988 | 27,933 | 29,878 |
| 2 | 27,933 | 33,778 | 39,622 | 45,467 |
| 3 | 33,778 | 45,467 | 57,147 | 68,826 |
| 4 | 41,572 | 61,041 | 80,505 | 99,982 |
| 5 | 51,304 | 80,505 | 109,717 | 138,921 |
| 6 | 62,987 | 103,876 | 144,751 | 185,639 |

**Fitted** against the area under the levels, n(n+1)/2, for each rise:

| Rise | Floor | Floor in blanks | Slope | Slope over rise | R² |
|---|---|---|---|---|---|
| 1 | 21,832 | 4.719 | 1,965.5 | 1,965.5 | 0.99966 |
| 2 | 21,830 | 4.719 | 3,912.6 | 1,956.3 | 0.99991 |
| 3 | 21,830 | 4.719 | 5,859.3 | 1,953.1 | 0.99996 |
| 4 | 21,831 | 4.719 | 7,806.4 | 1,951.6 | 0.99998 |

**Against the seal.**

- S1, every reading identical across runs, so the scaling is definite: **confirmed**.
- S2, the slope scales with the rise (slope over rise the same to two parts in a hundred): **confirmed**; they agree to
  seven parts in a thousand.
- S3, the floor does not scale with the rise: **confirmed**. The four floors agree to one part in ten thousand, and each
  is within three parts in a hundred of the reading at level 0.
- S4, a straight line in the area at each rise: **confirmed**, R² above 0.9996 throughout.
- S5 (recorded): the floor is 4.72 blanks.

**What it says.** The enumeration provides the scaling, as the author said it would. On the meter the reading is a
floor and a slope; the slope goes as the rise and the floor does not move. Two tapes with the same number of cells read
the same whatever rise and level made them (27,933 at rise 1 level 2 and at rise 3 level 1; 33,778 at rise 1 level 3
and at rise 2 level 2), so the reading is a function of the cells alone: about 21,260 for no cells, some 850 more for
the first, and about 1,950 a cell after. So on the count nothing of the temperature stays behind when the rise is
changed, and on the meter the floor does. In blanks the floor is 4.72, not one.

**Standing.** The heartbeats are *measured*, on one machine; the fits are *computed*. That a tape of that many cells of
the device's truth, each clicked once, is the meter's reading of the temperature at that rise and level is Claude's
choice of workload, and the author may correct it.

## Experiment 013: number go up

**Setup:** `4bd969e` (`readings/013-number-go-up/`). **Source:** `40da726`. **Read:** Apple M2, 18 November 2026, five
runs, one fresh process each; `raw/M2/readings.out`. The probe compiled as sealed (after one repair made before the
seal and recorded in it).

**The author's statement:** "the reader can only read what is in the compile. so make an experiment with the timer in
the code that demonstrates that the time does increase between a single evaluation and lots of evaluations. that's all
you need, number go up."

**Read.** One evaluation is the device's truth, one cell, clicked once, elaborated and reduced to weak head normal
form. The clock and the heartbeats were read inside the elaboration, around 1, 10, 100 and 1000 evaluations:

| Evaluations | Heartbeats (all five runs) | Nanoseconds, least | Nanoseconds, greatest |
|---|---|---|---|
| 1 | 23,248 | 2,153,042 | 4,756,167 |
| 10 | 221,480 | 5,583,917 | 6,943,833 |
| 100 | 2,219,187 | 56,350,458 | 60,601,750 |
| 1000 | 22,236,787 | 571,582,875 | 679,980,708 |

**Against the seal.**

- S1 (the author's), a thousand evaluations take more nanoseconds than one, in every run: **confirmed**. The least
  ratio is 120 and the greatest 314.
  *Erratum, 19 November 2026.* The statement is about each run. From `raw/M2/readings.out` the five ratios of a
  thousand evaluations to one, run by run, are 120, 231, 132, 267 and 269. The least is 120 and the greatest is 269.
  The 314 was one run's thousand over another run's one and should not have been given. S1 is confirmed as before.
- S2, the nanoseconds increase at every step in every run: **confirmed**.
- S3, the heartbeats increase at every step and are identical across runs; the nanoseconds are not: **confirmed**.
- S4, the first evaluation costs more than a later one: **confirmed**. One evaluation alone read 2.2 to 4.8 million
  nanoseconds; a thousand read 0.57 to 0.68 million each.
- S5 (recorded): heartbeats an evaluation are 23,248; 22,148; 22,192; 22,237 at the four counts.

**What it says.** Number go up. A reader of the compile reads, in the compile's own output, that many evaluations
took longer than one, on both meters. The heartbeats say the same thing every run; the nanoseconds say more every
time and a different amount each run. The heartbeats an evaluation are not constant: the first costs about 1,100
more than a later one, and the later ones rise slightly with the count. That is recorded and not explained.

**Standing.** The readings are *measured*, on one machine. That the reader can only read what is in the compile is
the author's (*declared*). What an evaluation is, here, is Claude's choice of workload, and the author may correct it.

## Experiment 014: the two decisions

**Setup:** `a3abd0f` (`readings/014-the-two-decisions/`). **Source:** `fe5cf5d`. **Read:** Apple M2, 18 November 2026,
five runs, two probes (one for each order), one fresh process per probe per run; `raw/M2/readings.out`. Both probes
compiled as sealed (after one repair made before the seal and recorded in it).

**The author's statement:** "the reader can only read what is in the compile."

**Read.** One evaluation is the device's root for a decision, `you_re_a_daisy_if_you_do (bitFACT decision)`,
elaborated and reduced to weak head normal form. In each compile: a blank, then one decision once and a thousand
times, then the other once and a thousand times. Heartbeats, identical in all five runs:

| | Decision true | Decision false |
|---|---|---|
| Evaluated first, once | 3,930 | 3,916 |
| Evaluated first, a thousand times | 2,952,063 | 2,952,063 |
| Evaluated second, once | 3,736 | 3,720 |
| Evaluated second, a thousand times | 2,952,093 | 2,952,093 |

The blank read 4,186 every time. Nanoseconds at a thousand evaluations: decision true, 60,069,166 to 64,129,708;
decision false, 60,022,500 to 63,384,042.

**Against the seal.**

- S1, at a thousand evaluations the heartbeats of the two decisions are not equal, and each is identical across
  runs and orders: **refuted**. In the same place in the compile they are equal, 2,952,063 first and 2,952,093
  second, whichever decision it is; and they are not the same across the two orders. They are identical across runs.
- S2, the decision true costs more heartbeats: **refuted** at a thousand, where they are equal. At one evaluation it
  does: 14 more when evaluated first, 16 more when evaluated second.
- S3, the nanoseconds at a thousand do not separate the decisions: **confirmed**; the two ranges overlap.
- S4 (recorded): an evaluation among a thousand costs 2,952 heartbeats, either decision.

**What it says.** The timer tells the two decisions apart only on the first evaluation of each, by 14 or 16
heartbeats in about 3,900. After that it does not: a thousand evaluations of one decision cost exactly what a
thousand of the other cost in the same place. Where in the compile an evaluation stands moves the reading far more
than the decision does (about 190 at one evaluation, 30 at a thousand). The nanoseconds do not tell them apart at
all. So a reader of the timer can recover the decision only if it catches the first evaluation and knows its place.
Why the first evaluation differs and the later ones do not is not known.

**Standing.** The readings are *measured*, on one machine. Two of Claude's three sealed statements were refuted.
This does not touch Episode 13's theorem, which is about the evidence it names; it says the timer is not in that
evidence, and that on the first evaluation the timer reads more.

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
