-- (Gauge phase) Relocated under `Measurement/Gauge/` — this is a pure catalog-DISPLAY leaf (all `#eval`,
-- no computation), importing the physics one-way; nothing imports it. The reporting layer, made a directory.
import Measurement.AffineConstant

/-! # CalibrationManifest — the exact-spine / quantization-fence boundary, made EXPLICIT.

(Named `CalibrationManifest`, NOT `Calibration`: `Measurement.Calibration.*` is the sacred EKG/LeanCalibration
subsystem the early Episodes import — this manifest must not intrude on that namespace.)

Operator (2026-07-22): "move what can be moved out" — make the exact-rational-α-spine vs
lossy-readout-quantization boundary explicit in the tree. The literal physical MOVE is blocked by an
import cycle (the quantization methods are intrinsic to the domain objects — an `ApparatusRatio` knows how
to floor itself — and the defining Episodes use them internally: Ep26's calibration report, Ep32's
orbit-radius `.ceil`, Ep40's α-readout `.inverseScaledFloor`). So the boundary is DECLARED here, not moved.

This module IMPORTS the Episodes and CATALOGS the boundary. It MOVES NOTHING (zero def relocations) and is
a LEAF — nothing imports it, it imports the spine one-way, so it adds NO cycle.

## The honest THREE-layer map (more honest than "exact until readout")

The independent arithmetic sweep found: no floating point anywhere, exact Nat/Int rational arithmetic,
quantized "only at readout." The import-cycle obstruction proved that one-boundary picture IMPRECISE —
there is a quantization fence at BOTH ends of the spine:

  FENCE 1 — INPUT quantization:  apparatus (continuous ratios) → INTEGER inputs (R, C, T), via `.ceil`/
                                 `.floor`. Principled (it is HOW you read an integer from the apparatus),
                                 but it IS a quantization, INSIDE the spine at the input, not a readout.
        ↓
  EXACT-RATIONAL SPINE:          given those integers, the α computation is exact rational — `div`
                                 (cross-multiply) and `divNat` (denominator-multiply) are LOSSLESS. No
                                 approximation in the middle.
        ↓
  FENCE 2 — READOUT quantization: α (exact ratio) → SCALED-INTEGER readout (×1e18), via `.scaledFloor`/
                                 `.inverseScaledFloor`. The display resolution.

So the honest flagship claim is NOT "exact, no approximation until readout" but "EXACT-RATIONAL MIDDLE
between a principled input-quantization (the R/C/T ceils) and a readout-quantization (the α floors)."

## Remainder-standardization (this pass)

Every quantization primitive now keeps its remainder ALONGSIDE (floors travel with remainders — no
information silently destroyed): `.floor`/`.remainder`, `.inverseFloor`/`.inverseRemainder`,
`.scaledFloor`/`.scaledRemainder`, `.ceil`/`.ceilRemainder`, `.inverseScaledFloor`/
`.inverseScaledRemainder`. All companion values leave the floors/ceils unchanged. (The halfPi truncation
that once appeared here is RETIRED with the Ep25 π/2 crank — π is now MEASURED off the orbit, `ArchimedesPi`.)

## NOT calibration (stays for FIX-IN-PLACE, never laundered here)

The two Ep40 sites that DISTORTED the coupling — `tangeAtDistance`'s d<1 clamp and `inverseScaledFloor`'s
pole `/0 → 0` — are now PROJECTIVELY TOTALIZED (Batch 2, 2026-07-23): `ApparatusRatio` is extended to the
projective points (`0/0` indeterminate, `n/0` at infinity), tange returns the `0/0` sentinel off-domain
and the pole flows through the explicit `n/0` `reciprocal`, with on-domain-equivalence PROVEN byte-identical
(`inverseScaledFloor_eq`, `tangeAtDistance_on_domain`) so the jar never moved. The remaining fix-in-place
items are now ALSO discharged: Ep27 `cavendishSeparation − cavendishArm` PROVED nonneg (Batch 3,
`cavendishArm_le_cavendishSeparation`, = `boxCount`); Ep30 variance numerator given a signed companion
(Batch 4, `slipPointVarianceNumeratorSigned`, nonneg by Cauchy–Schwarz on genuine moments = marked); Ep39
`natAbsDiff` given the orientation-preserving `signedDiff` companion (Batch 4). This manifest declared the
boundary; it never laundered a distortion under a calibration name — each was fixed in place instead.
-/

namespace Measurement.Gauge.CalibrationManifest
open Measurement Measurement.AffineConstant

-- ── FENCE 1 — INPUT quantization: apparatus → integer inputs (principled, spine-resident) ──
#eval s!"[FENCE 1 — INPUT quantization] apparatus → integers: deviceG = {deviceG.numerator}/{deviceG.denominator} (Ep26 assay, rfl-computed) ; R = naturalUnitOrbitRadius = {naturalUnitOrbitRadius} (Ep32, via .ceil) ; T = firstSlipTargetBetweenOneAndTwo = {firstSlipTargetBetweenOneAndTwo} (Ep29, via slip .floor)"

-- ── EXACT-RATIONAL SPINE — the middle: exact given the integers (div/divNat lossless) ──
#eval s!"[SPINE — exact rational] k = τ/R² = {kNum}/{kDen} ; α map = Episode40 alphaFromSecondVariationAtDistance (div/divNat exact) ; jar (device's own inv-α) = math {reference} at count-3, physical Episode40 ≈ 137.011 — exact rational, NO approximation in the middle"

-- ── FENCE 2 — READOUT quantization: α → scaled-integer (×1e18) readout ──
#eval s!"[FENCE 2 — READOUT quantization] the α floors: .scaledFloor / .inverseScaledFloor (×1e18 display resolution) ; each now with a remainder companion (info-preserving)"

-- ── remainder-standardization: every quantization primitive keeps its remainder ──
#eval s!"[remainder-standardization] pairs kept: floor/remainder, inverseFloor/inverseRemainder, scaledFloor/scaledRemainder, ceil/ceilRemainder, inverseScaledFloor/inverseScaledRemainder — floors travel with their remainders, no info silently destroyed"

-- ── NOT laundered here (declared, not filed as calibration) ──
#eval "[NOT calibration — fix-in-place / proof-debt] ALL DISCHARGED: Ep40 tangeAtDistance d<1 clamp + inverseScaledFloor pole → PROJECTIVELY TOTALIZED (Batch 2; 0/0, n/0; on-domain byte-identical, jar held); Ep27 cavendishSeparation−cavendishArm → PROVED nonneg = boxCount (Batch 3); Ep30 variance numerator → signed companion, CS-nonneg marked (Batch 4); Ep39 natAbsDiff → signedUnit/orientation companion (Batch 4; erratum 2026-07-24: the companion lands as the signedUnit+orientation structure — the description bends to the code). Each FIXED IN PLACE, never laundered as calibration — jar held byte-identical throughout."

end Measurement.Gauge.CalibrationManifest
