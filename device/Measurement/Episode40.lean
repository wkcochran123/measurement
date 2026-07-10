import Measurement.Episode39ElectromagneticCoupling

/- MEANWHILE 40 -- ASK THE DEVICE FOR ALPHA. The Meissner electro/magnetic
calibration tape from Episode39.5 is now in hand, so the four-channel second variation
from Episode39 can be contracted to the dimensionless coupling in the
`h = c = 1` normalization.

The raw elaboration charge cancels against the field charge. What remains is:

  alpha = (1 - 1/r) * (1/r^2) / orbitUnit.

Here `1/r` is the potential channel, `1/r^2` is the field-per-charge channel at
the slip seam, and `orbitUnit = 18` is the natural orbit unit. The selected
Meissner electro/magnetic coefficient is carried as the calibration cell for this
contraction; it is generated before the alpha read rather than inferred after it.
-/

namespace Measurement

def inverseRadiusAtDistance (distance : RationalDistance) : ApparatusRatio :=
  { numerator := distance.denominator
    denominator := distance.numerator }

def tangeAtDistance (distance : RationalDistance) : ApparatusRatio :=
  { numerator := distance.numerator - distance.denominator
    denominator := distance.numerator }

def fieldPerChargeAtSlip (targetSlip : Nat) : ApparatusRatio :=
  { numerator := targetSlip
    denominator := naturalUnitOrbitRadius }

def alphaFromSecondVariationAtDistance
    (targetSlip : Nat) (distance : RationalDistance) : ApparatusRatio :=
  ((tangeAtDistance distance).mul (fieldPerChargeAtSlip targetSlip)).divNat
    naturalUnitOrbitRadius

def ApparatusRatio.inverseScaledFloor (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.denominator * scale / q.numerator

structure AlphaSecondVariationReport where
  normalization : String
  orbitUnit : Nat
  targetSlip : Nat
  distance : RationalDistance
  distanceScaledAt18 : Nat
  rawCharge : ApparatusRatio
  normalizedCharge : ApparatusRatio
  inverseRadius : ApparatusRatio
  tange : ApparatusRatio
  fieldPerCharge : ApparatusRatio
  electromagneticCoupling : ElectromagneticCouplingCoefficient
  electromagneticCouplingFactorScaledAt18 : Nat
  electromagneticCalibrationTapeLength : Nat
  couplingGeneratedBeforeAlpha : Bool
  maxwellSpeedOfLightEnforced : Bool
  maxwellSpeedOfLightSquaredScaledAt18 : Nat
  maxwellNaturalUnitVelocitySquaredScaledAt18 : Nat
  maxwellLorentzBoundaryVelocitySquaredScaledAt18 : Nat
  magneticRepulsionHasPhotonRecoilResponse : Bool
  magneticPhotonIncidentResponseResidueScaledAt18 : Nat
  magneticPhotonRecoilCarried : Bool
  alpha : ApparatusRatio
  alphaScaledAt18 : Nat
  inverseAlphaScaledAt18 : Nat
deriving Repr

def alphaSecondVariationReport
    (report : ChargeSecondVariationReport) : AlphaSecondVariationReport :=
  let slip := report.slipPoint
  let distance := slip.midpointDistance
  let inverseRadius := inverseRadiusAtDistance distance
  let tange := tangeAtDistance distance
  let fieldPerCharge := fieldPerChargeAtSlip slip.targetSlip
  let alpha := alphaFromSecondVariationAtDistance slip.targetSlip distance
  { normalization := "h = c = 1"
    orbitUnit := naturalUnitOrbitRadius
    targetSlip := slip.targetSlip
    distance := distance
    distanceScaledAt18 := distance.scaledFloor (pow10 18)
    rawCharge := report.rawCharge.magnitude
    normalizedCharge := report.normalizedCharge.magnitude
    inverseRadius := inverseRadius
    tange := tange
    fieldPerCharge := fieldPerCharge
    electromagneticCoupling := electromagneticCouplingSelected
    electromagneticCouplingFactorScaledAt18 :=
      electromagneticCouplingSelected.factorScaledAt18
    electromagneticCalibrationTapeLength :=
      electromagneticCalibrationTape.length
    couplingGeneratedBeforeAlpha :=
      electromagneticCouplingCalibrationReport.generatedBeforeFirstAlpha
    maxwellSpeedOfLightEnforced :=
      electromagneticCouplingCalibrationReport.maxwellSpeedOfLightEnforced
    maxwellSpeedOfLightSquaredScaledAt18 :=
      maxwellSpeedOfLightCertificate.speedOfLightSquaredScaledAt18
    maxwellNaturalUnitVelocitySquaredScaledAt18 :=
      maxwellSpeedOfLightCertificate.naturalUnitVelocitySquaredScaledAt18
    maxwellLorentzBoundaryVelocitySquaredScaledAt18 :=
      maxwellSpeedOfLightCertificate.lorentzBoundaryVelocitySquaredScaledAt18
    magneticRepulsionHasPhotonRecoilResponse :=
      electromagneticCouplingCalibrationReport.magneticRepulsionHasRecoilAndResponse
    magneticPhotonIncidentResponseResidueScaledAt18 :=
      magneticPhotonExchangeReport.incidentResponseResidueScaledAt18
    magneticPhotonRecoilCarried :=
      magneticPhotonExchangeReport.recoilCarriedByCooperPair
    alpha := alpha
    alphaScaledAt18 := alpha.scaledFloor (pow10 18)
    inverseAlphaScaledAt18 := alpha.inverseScaledFloor (pow10 18) }

def defaultAlphaSecondVariationReport? :
    Option AlphaSecondVariationReport :=
  defaultChargeSecondVariationReport?.map alphaSecondVariationReport

#eval defaultAlphaSecondVariationReport?

end Measurement
