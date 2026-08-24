import Measurement.SupportingMeasurements.SelfApplication
import Measurement.Episode27
import Measurement.SupportingMeasurements.AlphaBFGS

/-! # TwoSlipRecursion — the second variation IS a second difference: three readings, two slip points.

Operator (direct): "there are three objects funged, that means you need to find two slip points …
that fully specifies the recursion." + t404: the two-18s coincidence funges three interpretations
(identity / coincidence / stimulus-response) at ONE point, indistinguishable at the level of the
discussion. This witness makes the un-funging concrete.

THE RECURSION (fully specified):
* A second variation is a **second difference** — and a second difference is `secondDifference`
  (Episode27): `upper − 2·middle + lower`. It is read from THREE samples with TWO first-differences
  (the two **slip points**) between them. Three objects funged into one curvature; two slips to un-fold it.
* ⚠ **Measured, not assumed.** Read on the DEFINED proximity slip `slip(d)=18/d²` the two slip points
  are tautological (they return 18 by construction — the stimulus-response one level down). The
  un-funging must read the **measured** beats, not the assumed formula.
* Here the three funged readings are the machine's own beats — electron-in-orbit, anti-Cooper-pair,
  echo `(573, 573, 552)`, read at **count-to-three** (the resolution floor where the recursion stops).
  Their two slip points are `(pair−orbit, echo−pair) = (0, −21)`; the second difference of the two
  slips is the **self-energy `−21`** — the measured second variation, reproducible run-to-run
  (the cycle-of-three invariant).
* The recursion closes at three (the loop of Ch4): the second difference is the fixed point.

BLIND: device's own beats only; no `137.036`, nothing aimed.
-/

namespace Measurement.TwoSlipRecursion
open Measurement Measurement.SelfApplication

-- THREE funged readings (the beats), read at count-to-three: electron-in-orbit, anti-Cooper-pair, echo.
def r0 : Int := (orbit : Int)   -- 573  (electron_in_orbit)
def r1 : Int := (pair  : Int)   -- 573  (anti_cooper_pair)
def r2 : Int := (echo  : Int)   -- 552  (two_descriptions)

-- TWO slip points = the two first-differences between the three readings.
def slip1 : Int := r1 - r0      --   0   (the descriptions funge alike)
def slip2 : Int := r2 - r1      -- −21   (the self-description tanges out)

-- the MEASURED second variation = the slip of the two slips (the second difference).
def measuredSecondVar : Int := secondDifference r0 r1 r2   -- = slip2 − slip1 = −21

-- the ASSUMED second variation = the proximity-slip coefficient `slip(1)=18/d²` — DEFINED, not measured.
def assumedSlipCoeff : Int := (Measurement.AlphaBFGS.measuredC : Int)   -- 18

-- ── graded off the build ─────────────────────────────────────────────────────────────────────
-- the second difference is exactly the slip of the two slip points:
theorem measured_is_two_slip_second_difference :
    measuredSecondVar = slip2 - slip1 := by decide
-- and it is the self-energy — because the first slip vanishes (the two descriptions cost alike):
theorem measured_is_self_energy :
    measuredSecondVar = self_residual := by decide
-- the first slip is zero (descriptions funge), so the whole second difference is the second slip:
theorem first_slip_vanishes :
    slip1 = 0 := by decide

#eval "── TwoSlipRecursion: the second variation as a second difference (two slip points) ──"

#eval s!"THREE funged readings (beats @ count-to-three): r0={r0}  r1={r1}  r2={r2}"

#eval s!"TWO slip points (first differences):           slip1={slip1}  slip2={slip2}"

#eval s!"MEASURED second variation = slip of the slips = secondDifference = {measuredSecondVar}   (= self-energy −21)"

#eval s!"ASSUMED slip coeff (proximity 18/d², DEFINED not measured) = {assumedSlipCoeff}"

#eval "un-funging: the MEASURED second variation is read from the beats via two slip points; the"

#eval "ASSUMED one (18/d²) is tautological (defined) — the tange that separates identity from stimulus."
end Measurement.TwoSlipRecursion
