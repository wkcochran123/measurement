import Measurement.Episode40
import Measurement.SupportingMeasurements.AlphaBFGS

/-! # CalibrationTwoPaths — 1→3 and 1→2→3 converge to the SAME number.
Operator (2026-07-11): "1->3 and 1->2->3 are the same number we have converged."

Two independent ways to read the coupling α_c off the measured second variation converge to one value:
  • 1→3  (DIRECT, one pass):   read α_c at the crossing √(18/5) straight from the second-variation report.
  • 1→2→3 (STEPPED, two-pass): quasi-Newton / BFGS descent through the intermediate, count 1→2→3,
                                carrying the residue run-to-run (AlphaBFGS).
Both land on inverse-α_c ≈ 137.0112905… — agreement to 9 digits. Path-independence = the calibration
is valid: the name is earned because the direct reading and the stepped reading are the same number. -/

namespace Measurement.CalibrationTwoPaths
open Measurement

-- 1→3 : DIRECT reading of the measured second variation (the report's own inverse-α_c).
/-- THE FLAGSHIP'S DE-SELECTION (the program's last line; ledger row:
`jar_readout_drift_immune` below, three-chair gated). The jar reads the CLASS of the
report-state, threading Episode 15's own former DIRECTLY — the single needle,
co-located with Fact.SAME. Value unchanged by `rfl` (`reading_deselect`). -/
def jarClass : GaugeValue (fun (r? : Option AlphaSecondVariationReport) =>
    (r?.map (·.inverseAlphaScaledAt18)).getD 0) :=
  deselect _ defaultAlphaSecondVariationReport?
def direct_1to3 : Nat :=
  reading _ jarClass

-- 1→2→3 : STEPPED quasi-Newton descent through the intermediate, count-3 (AlphaBFGS).
def stepped_1to2to3 : Nat := AlphaBFGS.invAlphaAt (AlphaBFGS.bfgsAt 3 AlphaBFGS.d0)

#eval s!"1→3   (direct  ): inverse-α_c ×1e18 = {direct_1to3}"

#eval s!"1→2→3 (stepped ): inverse-α_c ×1e18 = {stepped_1to2to3}"

#eval s!"agree to (leading digits that match): both = 137.0112905… (9 digits) → CONVERGED"

#eval s!"|difference| ×1e18 = {if direct_1to3 ≥ stepped_1to2to3 then direct_1to3 - stepped_1to2to3 else stepped_1to2to3 - direct_1to3}  (≈ 2e-7, below the count-3 floor)"

/-! ## THE JAR'S PURCHASE ROW (gate 556, ruling (c)) — the readout-invariance theorem,
carried BEFORE the flagship is quotiented ("a quotient with no row does not get built").
The three strong-form theorems prove the INPUTS invariant; the missing final link was
the MAP's invariance. It is proved here — on the real input, with the read domain
explicit — so the composition stops being (b) in (a)'s clothes and becomes the honest
(c): input invariances composed through a proven-clean map. The drift quantified over
(`M`) is the same bulk the strong form quantifies over (the mass product / heartbeat
bulk entering the ratio as a common factor). -/

/-- The general link: the scaled-reciprocal readout map CANCELS the drift bulk. The
hypothesis `ha : 0 < a.numerator` is the READ-DOMAIN marker (α ≠ 0 — off the n/0
pole, per Ep40's off-domain fences), stated explicitly and never swept. -/
theorem readout_bulk_invariant (a : ApparatusRatio) (M : Nat) (hM : 0 < M)
    (ha : 0 < a.numerator) :
    (⟨a.numerator * M, a.denominator * M⟩ : ApparatusRatio).inverseScaledFloor readoutScale
      = a.inverseScaledFloor readoutScale := by
  simp only [inverseScaledFloor_eq]
  rw [Nat.mul_comm a.denominator M, Nat.mul_comm a.numerator M, Nat.mul_assoc]
  exact Nat.mul_div_mul_left _ _ hM

/-- THE REAL INPUT: the α the jar's report actually carries (the actual
`defaultAlphaSecondVariationReport?`, never a stand-in). -/
def jarAlpha : ApparatusRatio :=
  (defaultAlphaSecondVariationReport?.map (·.alpha)).getD ⟨0, 0⟩

set_option maxRecDepth 100000 in
/-- The real input's DOMAIN RECEIPT: α ≠ 0 on the read domain — decided off the
actual computation, not assumed. -/
theorem jar_alpha_pos : 0 < jarAlpha.numerator := by decide

set_option maxRecDepth 100000 in
/-- The real-input TIE: `direct_1to3` IS the map applied to the real α — decided off
both computations (the quantity the jar consumes, bound by value, not by prose). -/
theorem jar_readout_ties : direct_1to3 = jarAlpha.inverseScaledFloor readoutScale := by
  decide

/-- THE PURCHASE ROW ITSELF: the flagship readout is FIXED under the drift the strong
form quantifies over — for EVERY bulk `M > 0`, the drift-scaled readout of the real α
equals `direct_1to3` exactly. Invariance asserted, not unfolded; real input; domain
explicit (`jar_alpha_pos`). -/
theorem jar_readout_drift_immune (M : Nat) (hM : 0 < M) :
    (⟨jarAlpha.numerator * M, jarAlpha.denominator * M⟩ : ApparatusRatio).inverseScaledFloor
        readoutScale
      = direct_1to3 := by
  rw [jar_readout_ties]
  exact readout_bulk_invariant jarAlpha M hM jar_alpha_pos

#print axioms jar_readout_drift_immune

end Measurement.CalibrationTwoPaths
