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
| 004 | `readings/004-relative-time` | the four rulers (universe level, heartbeats, time) combined into relative time through the field equations' weak-field limit | `03e888c` | M2 and M2 Ultra read |
| 005 | `readings/005-two-variations` | the two representations of the first variation, time-like (local) and space-like (the potential), and the convective term that joins them | `96a1898` | M2 and M2 Ultra read |
| 006 | `readings/006-frames` | frames as points: the M2 Ultra's performance and efficiency cores and the M2, on three workloads; the triangle's signed area; the convective term at thirty runs | `5a555d6` | read on the M2 Ultra (P and E); the M2 from 001, 002, 005 |
| 007 | `readings/007-fenceposts` | the five-block fencepost: does relative time on the ladder break at the posts 6, 11, …, 31 (seven panels of five, one post over)? | `4e5bb93` | read on the M2 Ultra; superseded by 007b |
| 007b | `readings/007b-fenceposts-both-ways` | the fencepost read both ways: do the posts beat the knot grid shifted backward as well as forward? | `a3ee8f2` | read on the M2 Ultra: refuted |
| 008 | `readings/008-two-routes` | two routes to one number: the crank (the derivative) and the halving (the sign only), each turn on the meter; do their total costs agree? | `3f797dc` | read on the M2: the heartbeat meter reads its floor for both routes; wall time separates them by 3.1 |
| 008b | `readings/008b-boot-count` | the boot count: what the first turn of a third loop reads (13, 18 or 8), whether the one heartbeat a turn is the meter's own post, and whether a loop with no device boots the same | the setup commit that adds the folder | sealed, not run |

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
arithmetic of either route. So the reading neither supports nor refutes conservation of cost between the routes; it
shows this meter cannot weigh them. The seal's choice of the first run of one probe as the comparison was a flaw in the
seal, and the second probe is what exposed it.

Wall time does separate the routes. The crank takes 3.1 times as long as the halving, in either order (3.07 and 3.10).
The crank's time per turn is level across all 106 turns, including the turns after it has halted; the halving's grows
as its numbers grow.

**Status.** Read on the M2. Not read on the M2 Ultra.

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
