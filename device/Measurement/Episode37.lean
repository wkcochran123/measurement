import Measurement.Episode36

/- MEANWHILE 37 -- ELABORATION COST IS ELECTRON CHARGE. The raw compiler pulse
is no longer ancillary telemetry. It is the electron's charge magnitude in
device units. The electron orientation supplies the sign, so the normalized unit
charge is the electron convention:

  charge magnitude = elaboration cost,
  signed charge    = -elaboration cost,
  charge unit      = -1.
-/

/-! # Meanwhile 37 — the charge: the electron's number, −1  (⊖ paymaster, debt in red) — MILESTONE

**The genre skin (⊖).** The paymaster totts up the elaborator's toil and enters it as a debt: the amount
owed is the magnitude, and because it was spent — a debit — it goes in RED, with a minus. One unit owed is
−1.

**Object & facet (MILESTONE — tracked-thread payoff #2).** This is the CHARGE facet of the object
Yang–Mills describes. In Ep32 the electron earned a ROOM; here it earns the NUMBER on the door, −1. Room
plus number: the electron is now doubly distinguished — the second independent witness for box 1 that the
naming (Ep25) could only assert is fully EARNED (Ep25 → Ep32 → Ep37). We describe the facet in the device's
own exact terms; we never open or solve Yang–Mills, and the last box stays wrapped.

**The squeeze (a PINNED equality).** The charge MAGNITUDE is pinned to the compiler's elaboration cost —
`electronElaborationChargeMagnitude = electronElaborationCost`, by `rfl` — and the sign convention fixes the
unit charge to −1 (`decide`).

**⚠️ Electron-scope + charge fence (hardest here).** Every "electron" is the DEVICE'S OWN test body, and its
"charge" is the compiler's ELABORATION COST — the toil the elaborator actually spent (Ep22's heartbeat) —
under our OWN sign convention. It is NOT real electric charge, NOT a real electron's minus-one, NOT
electromagnetism, NOT a coulomb of anything (literal, not a disavowal). The magnitude is cost; the sign is
our rule; the −1 is our debit mark.
-/

namespace Measurement

/-- `ElaborationChargeOrientation` — which side of the account a charge falls on: `electron` (the owing /
debit side), `positron` (the owed-to side), `neutral` (square). `Repr`, `DecidableEq`. -/
inductive ElaborationChargeOrientation where
  | electron
  | positron
  | neutral
deriving Repr, DecidableEq

/-- `elaborationChargeOrientationOfSign (x) : ElaborationChargeOrientation` — `x = 0 ↦ neutral`; `x < 0 ↦
electron` (the debit direction); `x > 0 ↦ positron`. A sign convention, ours. -/
def elaborationChargeOrientationOfSign (x : Int) : ElaborationChargeOrientation :=
  if x = 0 then .neutral else if x < 0 then .electron else .positron

/-- `electronElaborationCost : Nat` — the toil itself: the compiler's own elaboration heartbeat
(`theHeartRate`, from Ep22). -/
def electronElaborationCost : Nat :=
  theHeartRate

/-- `electronElaborationChargeMagnitude : Nat` — that cost, taken as the charge's magnitude
(`= electronElaborationCost`; theorem below). -/
def electronElaborationChargeMagnitude : Nat :=
  electronElaborationCost

/-- `electronElaborationSignedCharge : Int` — the debt entered as a debit, minus the cost
(`-(Int.ofNat electronElaborationChargeMagnitude)`). -/
def electronElaborationSignedCharge : Int :=
  -(Int.ofNat electronElaborationChargeMagnitude)

/-- `electronElaborationChargeUnit : Int` — one unit in the red, `-1`, whenever any toil was spent
(`0 < magnitude`); else `0`. -/
def electronElaborationChargeUnit : Int :=
  if 0 < electronElaborationChargeMagnitude then -1 else 0

/-- `electronElaborationCostRead : WheelStimulusRead` — the cost dropped onto the Ep25 wheel. -/
def electronElaborationCostRead : WheelStimulusRead :=
  wheelStimulusRead "electron.elaborationCost" (Int.ofNat electronElaborationCost)

/-- `electronElaborationSignedChargeRead : WheelStimulusRead` — the signed debt dropped onto the wheel. -/
def electronElaborationSignedChargeRead : WheelStimulusRead :=
  wheelStimulusRead "electron.signedElaborationCharge" electronElaborationSignedCharge

/-- `electronChargeConvention : Int` — the house rule that one unit of electron charge is `-1`. -/
def electronChargeConvention : Int :=
  -1

/-- `ElectronElaborationChargeReport` — the whole account: the cost and its wheel read, the charge
magnitude, the signed charge and its read, the unit, the convention, the orientation, and two checks —
`costIsChargeMagnitude` and `chargeUnitMatchesElectronConvention`. -/
structure ElectronElaborationChargeReport where
  elaborationCost : Nat
  costRead : WheelStimulusRead
  chargeMagnitude : Nat
  signedCharge : Int
  signedChargeRead : WheelStimulusRead
  chargeUnit : Int
  electronChargeConvention : Int
  chargeOrientation : ElaborationChargeOrientation
  costIsChargeMagnitude : Bool
  chargeUnitMatchesElectronConvention : Bool
deriving Repr

/-- `electronElaborationChargeReport : ElectronElaborationChargeReport` — draw up the account and check that
the magnitude really is the cost and the unit really matches the `-1` convention (both `decide`). -/
def electronElaborationChargeReport : ElectronElaborationChargeReport :=
  { elaborationCost := electronElaborationCost
    costRead := electronElaborationCostRead
    chargeMagnitude := electronElaborationChargeMagnitude
    signedCharge := electronElaborationSignedCharge
    signedChargeRead := electronElaborationSignedChargeRead
    chargeUnit := electronElaborationChargeUnit
    electronChargeConvention := electronChargeConvention
    chargeOrientation := elaborationChargeOrientationOfSign electronElaborationSignedCharge
    costIsChargeMagnitude :=
      (decide (electronElaborationChargeMagnitude = electronElaborationCost) : Bool)
    chargeUnitMatchesElectronConvention :=
      (decide (electronElaborationChargeUnit = electronChargeConvention) : Bool) }

/-- `electron_elaboration_cost_is_charge_magnitude`.
**Proposition:** `electronElaborationChargeMagnitude = electronElaborationCost` — the charge magnitude IS
the elaboration cost.
**Mechanism:** `rfl` — kernel-computed (definitionally equal).
**Squeeze role:** the charge magnitude pinned to the elaboration cost — the identity at the heart of it, the
charge IS the toil. -/
theorem electron_elaboration_cost_is_charge_magnitude :
    electronElaborationChargeMagnitude = electronElaborationCost := rfl

/-- `electron_elaboration_charge_orients_electron`.
**Proposition:** `elaborationChargeOrientationOfSign electronElaborationSignedCharge =
ElaborationChargeOrientation.electron` — the signed charge orients to the electron (debit) side.
**Mechanism:** `by decide` — kernel-evaluated.
**Squeeze role:** the sign fixed to the electron/debit direction — the number on the door is −1. -/
theorem electron_elaboration_charge_orients_electron :
    elaborationChargeOrientationOfSign electronElaborationSignedCharge =
      ElaborationChargeOrientation.electron := by
  decide

/-- `electron_elaboration_charge_unit_matches_convention`.
**Proposition:** `electronElaborationChargeUnit = electronChargeConvention` — the unit charge equals the
house `-1` convention.
**Mechanism:** `by decide` — kernel-evaluated.
**Squeeze role:** the unit pinned to −1 — the debit mark, ours, confirmed. -/
theorem electron_elaboration_charge_unit_matches_convention :
    electronElaborationChargeUnit = electronChargeConvention := by
  decide

/-! ## Readout — the account, settled
`#eval electronElaborationChargeReport` prints the whole account: the cost, the magnitude, the signed debt,
the unit, the orientation, and the two checks. The theorems above pin the magnitude to the cost and the unit
to −1. Two presents now bear the electron's name — the room (Ep32) and the number (−1). The next facet, the
field at the slip point, is next door. -/
#eval electronElaborationChargeReport

end Measurement
