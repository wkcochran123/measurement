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

namespace Measurement

def chargePotentialMagnitudeAtDistance
    (chargeMagnitude : Nat) (distance : RationalDistance) : ApparatusRatio :=
  { numerator := chargeMagnitude * distance.denominator
    denominator := distance.numerator }

def chargeFieldMagnitudeAtDistance
    (chargeMagnitude : Nat) (distance : RationalDistance) : ApparatusRatio :=
  { numerator := chargeMagnitude * square distance.denominator
    denominator := square distance.numerator }

def chargeFieldMagnitudeAtSlipBoundary
    (chargeMagnitude targetSlip : Nat) : ApparatusRatio :=
  { numerator := chargeMagnitude * targetSlip
    denominator := naturalUnitOrbitRadius }

def electronSlipPointChargeRead : WheelStimulusRead :=
  wheelStimulusRead "electron.slipPointCharge" electronElaborationSignedCharge

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
             midpointDistance.scaledFloor (pow10 18)
           signedCharge := electronElaborationSignedCharge
           chargeMagnitude := electronElaborationChargeMagnitude
           normalizedCharge := electronElaborationChargeUnit
           chargeOrientation :=
             elaborationChargeOrientationOfSign electronElaborationSignedCharge
           chargeRead := electronSlipPointChargeRead
           midpointPotentialMagnitude := potential
           midpointPotentialMagnitudeScaledAt18 :=
             potential.scaledFloor (pow10 18)
           midpointFieldMagnitude := midpointField
           midpointFieldMagnitudeScaledAt18 :=
             midpointField.scaledFloor (pow10 18)
           exactBoundaryFieldMagnitude := boundaryField
           exactBoundaryFieldMagnitudeScaledAt18 :=
             boundaryField.scaledFloor (pow10 18) } :
          SlipPointChargeReport)

def defaultSlipPointChargeReport? : Option SlipPointChargeReport :=
  slipPointChargeReport? firstSlipTargetBetweenOneAndTwo 128 48

theorem electron_slip_point_charge_is_elaboration_charge :
    electronSlipPointChargeRead.signedValue = electronElaborationSignedCharge := rfl

#eval defaultSlipPointChargeReport?

end Measurement
