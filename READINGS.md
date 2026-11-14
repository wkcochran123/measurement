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
| 001 | `readings/001-coupling` | heartbeats per device cell (the coupling g) and wall time per heartbeat (the dilation D) across machines | `5b8b720` | M2 read; M2 Ultra building |

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
   runs the same source on the same toolchain; only τ differs. *Result: pending.*

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
| 001 | `5b8b720` | Mac Studio | Apple M2 Ultra | 24 (16 + 8) | 64 GB | 26.6.2 | v4.27.0-rc1 | pending | pending | pending | pending | pending |

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
