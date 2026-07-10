import Measurement.Episode36

/- MEANWHILE 37 -- ELABORATION COST IS ELECTRON CHARGE. The raw compiler pulse
is no longer ancillary telemetry. It is the electron's charge magnitude in
device units. The electron orientation supplies the sign, so the normalized unit
charge is the electron convention:

  charge magnitude = elaboration cost,
  signed charge    = -elaboration cost,
  charge unit      = -1.
-/

namespace Measurement

inductive ElaborationChargeOrientation where
  | electron
  | positron
  | neutral
deriving Repr, DecidableEq

def elaborationChargeOrientationOfSign (x : Int) : ElaborationChargeOrientation :=
  if x = 0 then .neutral else if x < 0 then .electron else .positron

def electronElaborationCost : Nat :=
  theHeartRate

def electronElaborationChargeMagnitude : Nat :=
  electronElaborationCost

def electronElaborationSignedCharge : Int :=
  -(Int.ofNat electronElaborationChargeMagnitude)

def electronElaborationChargeUnit : Int :=
  if 0 < electronElaborationChargeMagnitude then -1 else 0

def electronElaborationCostRead : WheelStimulusRead :=
  wheelStimulusRead "electron.elaborationCost" (Int.ofNat electronElaborationCost)

def electronElaborationSignedChargeRead : WheelStimulusRead :=
  wheelStimulusRead "electron.signedElaborationCharge" electronElaborationSignedCharge

def electronChargeConvention : Int :=
  -1

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

theorem electron_elaboration_cost_is_charge_magnitude :
    electronElaborationChargeMagnitude = electronElaborationCost := rfl

theorem electron_elaboration_charge_orients_electron :
    elaborationChargeOrientationOfSign electronElaborationSignedCharge =
      ElaborationChargeOrientation.electron := by
  decide

theorem electron_elaboration_charge_unit_matches_convention :
    electronElaborationChargeUnit = electronChargeConvention := by
  decide

#eval electronElaborationChargeReport

end Measurement
