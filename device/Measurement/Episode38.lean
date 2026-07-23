import Measurement.Episode37

/- MEANWHILE 38 -- CHARGE AT THE SLIP POINT. The slip-point distance is still
the bracket measured in Episode35. The charge is the elaboration charge from
Episode37. This file keeps those two facts separate:

  charge at the point      = signed electron elaboration charge,
  potential read near it   = |q| / r,
  field read at the seam   = |q| / r^2.

The exact seam is rational for the field because the slip boundary is
18 / r^2 = targetSlip.
-/

/-! # Meanwhile 38 — the field at the slip point: X marks the charge  (✕ treasure map)

**The genre skin (✕).** Take the corridor's own map to the very place the steel first slipped (Ep29) — an X
the map has carried all along — and dig. What you unearth is a charge.

**Object & facet.** This is the charge-read-as-a-field-at-the-slip-location facet of the object Yang–Mills
describes. We describe the facet in the device's own exact terms; we never open or solve Yang–Mills, and the
last box stays wrapped.

**The squeeze (a PINNED equality — an internal IDENTITY).** The charge read AT the slip point is EXACTLY
the elaboration charge Ep37 promised: `electronSlipPointChargeRead.signedValue = electronElaborationSignedCharge`,
by `rfl`. This is one quantity under two names, not two independent routes: the slip-point read is *built
from* the elaboration charge (`wheelStimulusRead … electronElaborationSignedCharge`), so `.signedValue`
unwraps to that same input. Nothing new is discovered; the SAME charge, re-read where it was placed — the
device consistent with itself by construction, never sold as two witnesses. The potential `|q| / r` and field `|q| / r²` near X (exact at the seam, since the boundary
fixes `18` over `r²` at the target) are the readings taken there.

**⚠️ Fence (carried from Ep37).** This "field" and this "charge" are the device's OWN readings in its OWN
model — NOT a real electromagnetic field, NOT real field lines, NOT a real charge, NOT electromagnetism
(literal). The charge is still Ep37's elaboration cost under our own sign convention; reading it at a place
does not upgrade it to a world quantity.
-/

namespace Measurement

/-- `chargePotentialMagnitudeAtDistance (chargeMagnitude) (distance) : ApparatusRatio` — the "potential" near
the spot, `|q| / r`: numerator `chargeMagnitude * distance.denominator`, denominator `distance.numerator`. -/
def chargePotentialMagnitudeAtDistance
    (chargeMagnitude : Nat) (distance : RationalDistance) : ApparatusRatio :=
  { numerator := chargeMagnitude * distance.denominator
    denominator := distance.numerator }

/-- `chargeFieldMagnitudeAtDistance (chargeMagnitude) (distance) : ApparatusRatio` — the "field" near the
spot, `|q| / r²`: numerator `chargeMagnitude * square distance.denominator`, denominator
`square distance.numerator`. -/
def chargeFieldMagnitudeAtDistance
    (chargeMagnitude : Nat) (distance : RationalDistance) : ApparatusRatio :=
  { numerator := chargeMagnitude * square distance.denominator
    denominator := square distance.numerator }

/-- `chargeFieldMagnitudeAtSlipBoundary (chargeMagnitude) (targetSlip) : ApparatusRatio` — the exact field
right at the seam, `chargeMagnitude * targetSlip` over `naturalUnitOrbitRadius` — rational because the slip
boundary fixes `18` over `r²` at the target. -/
def chargeFieldMagnitudeAtSlipBoundary
    (chargeMagnitude targetSlip : Nat) : ApparatusRatio :=
  { numerator := chargeMagnitude * targetSlip
    denominator := naturalUnitOrbitRadius }

/-- `electronSlipPointChargeRead : WheelStimulusRead` — the charge read AT the spot: the Ep37 signed
elaboration charge dropped onto the wheel. This is what the dig turns up. -/
def electronSlipPointChargeRead : WheelStimulusRead :=
  wheelStimulusRead "electron.slipPointCharge" electronElaborationSignedCharge

/-- `SlipPointChargeReport` — the survey of the spot: the slip bracket found and closed in, the signed
charge, its magnitude, unit, and orientation, the charge read, and the potential and field at the midpoint
plus the exact field at the seam. -/
structure SlipPointChargeReport where
  targetSlip : Nat
  gridCells : Nat
  rungs : Nat
  lowerDistance : RationalDistance
  upperDistance : RationalDistance
  midpointDistance : RationalDistance
  midpointDistanceScaledAt18 : Nat
  signedCharge : Int
  chargeMagnitude : Nat
  normalizedCharge : Int
  chargeOrientation : ElaborationChargeOrientation
  chargeRead : WheelStimulusRead
  midpointPotentialMagnitude : ApparatusRatio
  midpointPotentialMagnitudeScaledAt18 : Nat
  midpointFieldMagnitude : ApparatusRatio
  midpointFieldMagnitudeScaledAt18 : Nat
  exactBoundaryFieldMagnitude : ApparatusRatio
  exactBoundaryFieldMagnitudeScaledAt18 : Nat
deriving Repr

/-- `slipPointChargeReport? (targetSlip) (gridCells) (rungs) : Option SlipPointChargeReport` — grid and
bisect for the slip (as Ep35), then read the Ep37 charge, the potential, and the field there; `none` if no
patch holds the seam. -/
def slipPointChargeReport?
    (targetSlip gridCells rungs : Nat) : Option SlipPointChargeReport :=
  match firstSlipGridCell targetSlip gridCells with
  | none => none
  | some cell =>
      let bracket :=
        bisectDyadicSlipAux rungs targetSlip
          (dyadicSlipBracketFromGridCell cell)
      let lowerDistance := bracket.lowerDistance
      let upperDistance := bracket.upperDistance
      let midpointDistance := bracket.midpointDistance
      let potential :=
        chargePotentialMagnitudeAtDistance
          electronElaborationChargeMagnitude midpointDistance
      let midpointField :=
        chargeFieldMagnitudeAtDistance
          electronElaborationChargeMagnitude midpointDistance
      let boundaryField :=
        chargeFieldMagnitudeAtSlipBoundary
          electronElaborationChargeMagnitude targetSlip
      some
        ({ targetSlip := targetSlip
           gridCells := gridCells
           rungs := rungs
           lowerDistance := lowerDistance
           upperDistance := upperDistance
           midpointDistance := midpointDistance
           midpointDistanceScaledAt18 :=
             midpointDistance.scaledFloor (readoutScale)
           signedCharge := electronElaborationSignedCharge
           chargeMagnitude := electronElaborationChargeMagnitude
           normalizedCharge := electronElaborationChargeUnit
           chargeOrientation :=
             elaborationChargeOrientationOfSign electronElaborationSignedCharge
           chargeRead := electronSlipPointChargeRead
           midpointPotentialMagnitude := potential
           midpointPotentialMagnitudeScaledAt18 :=
             potential.scaledFloor (readoutScale)
           midpointFieldMagnitude := midpointField
           midpointFieldMagnitudeScaledAt18 :=
             midpointField.scaledFloor (readoutScale)
           exactBoundaryFieldMagnitude := boundaryField
           exactBoundaryFieldMagnitudeScaledAt18 :=
             boundaryField.scaledFloor (readoutScale) } :
          SlipPointChargeReport)

/-- `defaultSlipPointChargeReport? : Option SlipPointChargeReport` — the standard run: target
`firstSlipTargetBetweenOneAndTwo`, 128 grid cells, 48 bisection rungs. -/
def defaultSlipPointChargeReport? : Option SlipPointChargeReport :=
  slipPointChargeReport? firstSlipTargetBetweenOneAndTwo 128 48

/-- `electron_slip_point_charge_is_elaboration_charge`.
**Proposition:** `electronSlipPointChargeRead.signedValue = electronElaborationSignedCharge` — the charge
read at the slip point equals the Ep37 elaboration signed charge.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the charge read AT the slip point IS the elaboration charge — an IDENTITY, not a second
independent route. `electronSlipPointChargeRead` is *built from* `electronElaborationSignedCharge`
(`wheelStimulusRead "electron.slipPointCharge" electronElaborationSignedCharge`), so its `.signedValue`
unwraps to that same input: one source read at the spot, not two witnesses agreeing. (Honest relabel —
the earlier "cross-check / SECOND route" framing was aspirational; mechanically it's the identity chain
`cost ≡ charge ≡ read`, the same no-name-bridge discipline that governs C/T/R: one quantity under several
names is never sold as several independent confirmations.) Not a real field or a real charge in the world. -/
theorem electron_slip_point_charge_is_elaboration_charge :
    electronSlipPointChargeRead.signedValue = electronElaborationSignedCharge := rfl

/-! ## Readout — the survey of the spot
`#eval defaultSlipPointChargeReport?` prints the whole survey: the slip bracket, the charge read at X, and
the potential and field there. The theorem above pins the match (X = the Ep37 charge). The next facet, the
second variation, is next door. -/
#eval defaultSlipPointChargeReport?

end Measurement
