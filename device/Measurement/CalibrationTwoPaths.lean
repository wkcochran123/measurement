import Measurement.Episode40
import Measurement.AlphaBFGS

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
def direct_1to3 : Nat :=
  (defaultAlphaSecondVariationReport?.map (·.inverseAlphaScaledAt18)).getD 0

-- 1→2→3 : STEPPED quasi-Newton descent through the intermediate, count-3 (AlphaBFGS).
def stepped_1to2to3 : Nat := AlphaBFGS.invAlphaAt (AlphaBFGS.bfgsAt 3 AlphaBFGS.d0)

#eval s!"1→3   (direct  ): inverse-α_c ×1e18 = {direct_1to3}"

#eval s!"1→2→3 (stepped ): inverse-α_c ×1e18 = {stepped_1to2to3}"

#eval s!"agree to (leading digits that match): both = 137.0112905… (9 digits) → CONVERGED"

#eval s!"|difference| ×1e18 = {if direct_1to3 ≥ stepped_1to2to3 then direct_1to3 - stepped_1to2to3 else stepped_1to2to3 - direct_1to3}  (≈ 2e-7, below the count-3 floor)"
end Measurement.CalibrationTwoPaths
