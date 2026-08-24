# Calibration folder

**The canonical calibration record lives at the repo root:
[`CALIBRATION_METHOD.md`](../../../CALIBRATION_METHOD.md).** It carries the
two-path method, the calibration certificate (2026-08-13, gated both chairs),
the four certified claims, the fences, and the night's refusals. This file is
only the folder's local rules — one record, not two that can disagree.

## The files

| File | What it is |
|---|---|
| `EKGBounded.lean` | The bounded elaboration probe machinery — machine-measurement under a small, explicit budget (the closing file's `ekg_probe` runs on this). |
| `LeanCalibration.lean` | The calibration frame in Lean. |
| `ReadoutFloors.lean` | The readout floors — where readings stop. |
| `BIAS_____.lean` | Bias record. |
| `jfnk_calibration_certificate.py` | The calibration certificate (runnable receipt; see the root record). Python/scipy, outside the Lean build. |
| `NewtonCrossing.lean` | The exact-rational Newton completion (axiom-free, `decide`; see the root record). |
| `fixed_point_sweep.py` | The gap exhibit: sweep the coefficient from the approximation (1000) to the forbidden dial (c\* = 1000.1781, what a display would need to recite the lab's 137.0357) — the display lane slides, the certified lane cancels (18k/k = 18 ∀k), and the fixed point of the device's own step stays at 137.011 at every λ. Injected lab-ward seeds flow home in one step. |
| `strange_attractor_plot.py` (+ `.png`) | Part 2's closing exhibit: the attractor proved superattracting (g′(d\*) = 0, quadratic convergence — every neighborhood seed flows to 137.011, the lab-ward seed included), the honest "strange" object labeled as the BASIN BOUNDARY (the degree-3 map's Julia set in ℂ), and the radius line scoped model-internal (bracket width 1/8; orbit radius 18, R² = 324; basin (0, ∞)) — never the lab's femtometer. |

## Standing rules for this folder

- New calibration artifacts are gated by both chairs before they land.
- Exact and float never mix: certified quantities are exact rational
  (Lean, or `Fraction` in Python); floats are display-only.
- The jar is read-only from here: nothing in this folder computes, moves, or
  re-pins it.
- Mathlib, if ever added, rides only in this folder's new files (operator
  license 2026-08-13, verbatim on the channel) and is its own gated
  infrastructure decision — the lakefile is untouched until that gate runs.
- **Surd-digits are not coupling-digits**: fine approximants of `√(18/5)` are
  mathematics inside the floor's walls; the jar is the stop.
