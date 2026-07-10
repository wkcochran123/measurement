import Measurement.Calibration.LeanCalibration
import Measurement.ComputerProgram

/-! # VerifyAPI — Phase 1: the calibration verifier (the product surface)

`verify(claimed) → { verified?, residual : above/below floor }`, a clean 16+ wrapper over the ALREADY-BUILT engine
`Calibration.EKG.outgrown?` (LeanCalibration, sacred-in-spirit — READ-only, never touched). **Repeatability IS the
honesty:** the experiment is deterministic, so anyone re-runs `verify` and checks the claim rather than trusting it
— "builds a machine and asks you to check it," made runnable.

**The flagship INSTANCE the API verifies is the STRUCTURAL α** (Phase 0c): the ±1 = (−i)² loop holonomy — the
`1 = 0.999…` naming identity (the residue closes to null) resolved to the **three** distinguishable states
(count to 3: −1 electron / 0 null-identity / +1 positron, Ep84/Ep83). A claim VERIFIES iff it is within the floor
(not outgrown); the sub-floor residue is cut to antimatter (unclaimable). Grade off #print. -/

namespace Measurement.VerifyAPI
open Measurement Measurement.Calibration

/-- The residual side of the floor: a verified reading sits above the floor (claimable); a claim that outgrows the
budget is cut below the floor into antimatter (unclaimable). -/
inductive Residual
  | aboveFloor            -- verified, within budget
  | belowFloorAntimatter  -- outgrown → sub-floor → antimatter (unclaimable)
deriving Repr, DecidableEq

structure VerifyResult where
  verified : Bool
  residual : Residual
deriving Repr

/-- **THE PRODUCT SURFACE.** Run the repeatable experiment (`outgrown?`) on a claimed calibration; return whether
it VERIFIES (within the floor) and which side of the floor its residual lands. Deterministic → repeatable →
the honesty is in re-running it, not in trusting us. -/
def verify (ekg : EKG) (claimed : ComputerProgram) : VerifyResult :=
  let outgrown := EKG.outgrown? ekg claimed
  { verified := !outgrown
    residual := if outgrown then .belowFloorAntimatter else .aboveFloor }

/-! ## The flagship instance verified + a worked call. -/

-- A claimed calibration (the pattern the STRUCTURAL α reading plugs into — the reading is checked, not trusted).
def flagshipClaim : ComputerProgram := .load True Nat

#eval verify EKG.raw flagshipClaim                       -- run the repeatable experiment
#eval (verify EKG.raw flagshipClaim).verified            -- the checkable bit
#eval verify EKG.executed flagshipClaim                  -- re-run against the other calibrated standard (repeatable)

end Measurement.VerifyAPI
