import Measurement.Episode39

/- MEANWHILE 39.5 -- MEISSNER ELECTROMAGNETIC COUPLING EXPERIMENT. Before the
apparatus asks for alpha, it must already have both sides of the coupling:

* the electric side, exposed by the four-channel second variation;
* the magnetic side, exposed by the corridor needle and Lorentz wobble.

The coefficient is therefore a calibration tape, not a value smuggled in after
the alpha read. The experiment is the Meissner read: the Cooper-pair surface
current must expel the applied magnetic field. In device units, the applied
field is the magnetic needle mean, and one shielding quantum is the Lorentz
wobble. The measured coefficient is therefore

  applied_magnetic_field / shielding_wobble.

The tape records the lower integer, the exact quotient/remainder cell, and the
upper integer. `Episode40` then consumes the exact Meissner cell when it
contracts the second variation to alpha.
-/

namespace Measurement

structure ElectromagneticCouplingCoefficient where
  wholeFactor : Nat
  numerator : Nat
  denominator : Nat
  factorScaledAt18 : Nat
deriving Repr, DecidableEq

def electromagneticCouplingNumerator
    (whole numerator denominator : Nat) : Nat :=
  whole * denominator + numerator

def electromagneticCouplingFactorScaledAt18
    (whole numerator denominator : Nat) : Nat :=
  if denominator = 0 then
    whole * pow10 18
  else
    electromagneticCouplingNumerator whole numerator denominator * pow10 18 /
      denominator

def electromagneticCouplingCoefficient
    (whole numerator denominator : Nat) :
    ElectromagneticCouplingCoefficient :=
  { wholeFactor := whole
    numerator := numerator
    denominator := denominator
    factorScaledAt18 :=
      electromagneticCouplingFactorScaledAt18 whole numerator denominator }

def preAlphaElectricFieldScaledAt18 : Nat :=
  match defaultChargeSecondVariationReport? with
  | some report => report.field.scaledAt18
  | none => 0

def preAlphaElectricPotentialScaledAt18 : Nat :=
  match defaultChargeSecondVariationReport? with
  | some report => report.potential.scaledAt18
  | none => 0

def preAlphaMagneticWobbleScaledAt18 : Nat :=
  lorentzOrbitBracketReport.wobbleScaledAt18

def preAlphaMagneticNeedleMeanScaledAt18 : Nat :=
  cavendishMagneticNeedle.needleMeanScaledAt18

def meissnerAppliedMagneticFieldScaledAt18 : Nat :=
  preAlphaMagneticNeedleMeanScaledAt18

def meissnerShieldingQuantumScaledAt18 : Nat :=
  preAlphaMagneticWobbleScaledAt18

def meissnerFluxExpulsionQuotient : Nat :=
  meissnerAppliedMagneticFieldScaledAt18 /
    meissnerShieldingQuantumScaledAt18

def meissnerFluxExpulsionRemainderScaledAt18 : Nat :=
  meissnerAppliedMagneticFieldScaledAt18 %
    meissnerShieldingQuantumScaledAt18

def electromagneticCoupledMagneticResidueScaledAt18
    (coefficient : ElectromagneticCouplingCoefficient) : Nat :=
  if coefficient.denominator = 0 then
    preAlphaMagneticWobbleScaledAt18 * coefficient.wholeFactor
  else
    preAlphaMagneticWobbleScaledAt18 *
      electromagneticCouplingNumerator
        coefficient.wholeFactor coefficient.numerator coefficient.denominator /
        coefficient.denominator

structure ElectromagneticCouplingTapeCell where
  coefficient : ElectromagneticCouplingCoefficient
  electricFieldScaledAt18 : Nat
  electricPotentialScaledAt18 : Nat
  magneticWobbleScaledAt18 : Nat
  magneticNeedleMeanScaledAt18 : Nat
  coupledMagneticResidueScaledAt18 : Nat
  generatedBeforeAlpha : Bool
deriving Repr

def electromagneticCouplingTapeCell
    (coefficient : ElectromagneticCouplingCoefficient) :
    ElectromagneticCouplingTapeCell :=
  { coefficient := coefficient
    electricFieldScaledAt18 := preAlphaElectricFieldScaledAt18
    electricPotentialScaledAt18 := preAlphaElectricPotentialScaledAt18
    magneticWobbleScaledAt18 := preAlphaMagneticWobbleScaledAt18
    magneticNeedleMeanScaledAt18 := preAlphaMagneticNeedleMeanScaledAt18
    coupledMagneticResidueScaledAt18 :=
      electromagneticCoupledMagneticResidueScaledAt18 coefficient
    generatedBeforeAlpha := true }

abbrev ElectromagneticCalibrationTape :=
  List ElectromagneticCouplingTapeCell

def electromagneticCouplingLowerInteger :
    ElectromagneticCouplingCoefficient :=
  electromagneticCouplingCoefficient meissnerFluxExpulsionQuotient 0 1

def electromagneticCouplingUpperInteger :
    ElectromagneticCouplingCoefficient :=
  electromagneticCouplingCoefficient meissnerFluxExpulsionQuotient.succ 0 1

def electromagneticCouplingSelected :
    ElectromagneticCouplingCoefficient :=
  electromagneticCouplingCoefficient
    meissnerFluxExpulsionQuotient
    meissnerFluxExpulsionRemainderScaledAt18
    meissnerShieldingQuantumScaledAt18

def meissnerExpelledMagneticFieldScaledAt18 : Nat :=
  electromagneticCoupledMagneticResidueScaledAt18
    electromagneticCouplingSelected

def meissnerResidualInternalFieldScaledAt18 : Nat :=
  natAbsDiff meissnerAppliedMagneticFieldScaledAt18
    meissnerExpelledMagneticFieldScaledAt18

def electromagneticCalibrationTape : ElectromagneticCalibrationTape :=
  [ electromagneticCouplingTapeCell electromagneticCouplingLowerInteger,
    electromagneticCouplingTapeCell electromagneticCouplingSelected,
    electromagneticCouplingTapeCell electromagneticCouplingUpperInteger ]

def maxwellSpeedOfLightSquaredScaledAt18 : Nat :=
  pow10 18

def maxwellNaturalUnitVelocitySquaredScaledAt18 : Nat :=
  (cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquaredScaledAt18

def maxwellLorentzBoundaryVelocitySquaredScaledAt18 : Nat :=
  lorentzOrbitBracketReport.boundary.velocitySquaredScaledAt18

def maxwellNaturalUnitVelocitySquaredIsC : Bool :=
  decide
    (maxwellNaturalUnitVelocitySquaredScaledAt18 =
      maxwellSpeedOfLightSquaredScaledAt18)

def maxwellLorentzBoundaryVelocitySquaredIsC : Bool :=
  decide
    (maxwellLorentzBoundaryVelocitySquaredScaledAt18 =
      maxwellSpeedOfLightSquaredScaledAt18)

def maxwellLorentzBoundaryLightlike : Bool :=
  decide
    (lorentzOrbitBracketReport.boundary.regime =
      LorentzOrbitRegime.lightlikeBoundary)

def maxwellElectricReadAvailable : Bool :=
  decide (0 < preAlphaElectricFieldScaledAt18)

def maxwellMagneticReadAvailable : Bool :=
  cavendishMagneticNeedle.deflectsTowardMass &&
    decide (0 < preAlphaMagneticWobbleScaledAt18)

def maxwellMeissnerInteriorCancelled : Bool :=
  decide (meissnerResidualInternalFieldScaledAt18 = 0)

def maxwellElectricAndMagneticShareLightCone : Bool :=
  maxwellNaturalUnitVelocitySquaredIsC &&
    maxwellLorentzBoundaryVelocitySquaredIsC &&
    maxwellLorentzBoundaryLightlike

def maxwellGaussElectricEnforced : Bool :=
  maxwellElectricReadAvailable &&
    maxwellElectricAndMagneticShareLightCone

def maxwellGaussMagneticEnforced : Bool :=
  maxwellMeissnerInteriorCancelled &&
    maxwellElectricAndMagneticShareLightCone

def maxwellFaradayInductionEnforced : Bool :=
  maxwellMagneticReadAvailable &&
    maxwellElectricAndMagneticShareLightCone

def maxwellAmpereMaxwellEnforced : Bool :=
  maxwellElectricReadAvailable &&
    maxwellMagneticReadAvailable &&
    maxwellElectricAndMagneticShareLightCone

def maxwellSpeedOfLightEnforced : Bool :=
  maxwellGaussElectricEnforced &&
    maxwellGaussMagneticEnforced &&
    maxwellFaradayInductionEnforced &&
    maxwellAmpereMaxwellEnforced

structure MaxwellSpeedOfLightCertificate where
  name : String
  interpretation : String
  cSetToOne : Bool
  naturalUnitRadius : Nat
  speedOfLightSquaredScaledAt18 : Nat
  naturalUnitVelocitySquaredScaledAt18 : Nat
  lorentzBoundaryVelocitySquaredScaledAt18 : Nat
  electricReadAvailable : Bool
  magneticReadAvailable : Bool
  meissnerInternalFieldCancelled : Bool
  electricAndMagneticShareLightCone : Bool
  gaussElectricEnforced : Bool
  gaussMagneticEnforced : Bool
  faradayInductionEnforced : Bool
  ampereMaxwellEnforced : Bool
  maxwellClosureEnforced : Bool
deriving Repr

def maxwellSpeedOfLightCertificate :
    MaxwellSpeedOfLightCertificate :=
  { name := "maxwell-speed-of-light-closure"
    interpretation :=
      "the electric and magnetic reads are forced onto the same light cone; in the device this is the Maxwell closure c = 1"
    cSetToOne := true
    naturalUnitRadius := naturalUnitOrbitRadius
    speedOfLightSquaredScaledAt18 :=
      maxwellSpeedOfLightSquaredScaledAt18
    naturalUnitVelocitySquaredScaledAt18 :=
      maxwellNaturalUnitVelocitySquaredScaledAt18
    lorentzBoundaryVelocitySquaredScaledAt18 :=
      maxwellLorentzBoundaryVelocitySquaredScaledAt18
    electricReadAvailable := maxwellElectricReadAvailable
    magneticReadAvailable := maxwellMagneticReadAvailable
    meissnerInternalFieldCancelled :=
      maxwellMeissnerInteriorCancelled
    electricAndMagneticShareLightCone :=
      maxwellElectricAndMagneticShareLightCone
    gaussElectricEnforced := maxwellGaussElectricEnforced
    gaussMagneticEnforced := maxwellGaussMagneticEnforced
    faradayInductionEnforced := maxwellFaradayInductionEnforced
    ampereMaxwellEnforced := maxwellAmpereMaxwellEnforced
    maxwellClosureEnforced := maxwellSpeedOfLightEnforced }

inductive MagneticPhotonLeg where
  | incidentMagneticField
  | cooperPairRecoil
  | reflectedResponse
deriving Repr, DecidableEq

structure MagneticPhotonExchangeRead where
  leg : MagneticPhotonLeg
  fieldScaledAt18 : Nat
  lightConeVelocitySquaredScaledAt18 : Nat
  magneticReadAvailable : Bool
deriving Repr

def magneticPhotonIncidentRead : MagneticPhotonExchangeRead :=
  { leg := .incidentMagneticField
    fieldScaledAt18 := meissnerAppliedMagneticFieldScaledAt18
    lightConeVelocitySquaredScaledAt18 :=
      maxwellLorentzBoundaryVelocitySquaredScaledAt18
    magneticReadAvailable := maxwellMagneticReadAvailable }

def magneticPhotonRecoilRead : MagneticPhotonExchangeRead :=
  { leg := .cooperPairRecoil
    fieldScaledAt18 := meissnerExpelledMagneticFieldScaledAt18
    lightConeVelocitySquaredScaledAt18 :=
      maxwellLorentzBoundaryVelocitySquaredScaledAt18
    magneticReadAvailable := maxwellMagneticReadAvailable }

def magneticPhotonResponseRead : MagneticPhotonExchangeRead :=
  { leg := .reflectedResponse
    fieldScaledAt18 := meissnerExpelledMagneticFieldScaledAt18
    lightConeVelocitySquaredScaledAt18 :=
      maxwellLorentzBoundaryVelocitySquaredScaledAt18
    magneticReadAvailable := maxwellMagneticReadAvailable }

def magneticPhotonIncidentResponseResidueScaledAt18 : Nat :=
  natAbsDiff magneticPhotonIncidentRead.fieldScaledAt18
    magneticPhotonResponseRead.fieldScaledAt18

def magneticPhotonResponseOnLightCone : Bool :=
  maxwellElectricAndMagneticShareLightCone &&
    decide
      (magneticPhotonResponseRead.lightConeVelocitySquaredScaledAt18 =
        maxwellSpeedOfLightSquaredScaledAt18)

def magneticPhotonResponseCancelsField : Bool :=
  decide (magneticPhotonIncidentResponseResidueScaledAt18 = 0)

def magneticPhotonRecoilCarried : Bool :=
  decide
    (magneticPhotonRecoilRead.fieldScaledAt18 =
      magneticPhotonResponseRead.fieldScaledAt18)

def magneticPhotonRepulsionModeled : Bool :=
  magneticPhotonResponseOnLightCone &&
    magneticPhotonResponseCancelsField &&
    magneticPhotonRecoilCarried &&
    maxwellMeissnerInteriorCancelled

structure MagneticPhotonExchangeReport where
  name : String
  interpretation : String
  photonMediatorPresent : Bool
  incident : MagneticPhotonExchangeRead
  cooperPairRecoil : MagneticPhotonExchangeRead
  reflectedResponse : MagneticPhotonExchangeRead
  incidentResponseResidueScaledAt18 : Nat
  responseOnLightCone : Bool
  responseCancelsAppliedField : Bool
  recoilCarriedByCooperPair : Bool
  internalMagneticFieldCancelled : Bool
  repulsionModeledWithRecoilAndResponse : Bool
deriving Repr

def magneticPhotonExchangeReport : MagneticPhotonExchangeReport :=
  { name := "magnetic-photon-recoil-response"
    interpretation :=
      "model magnetic repulsion as an incident photon read, a Cooper-pair recoil, and a reflected response on the Maxwell light cone"
    photonMediatorPresent := true
    incident := magneticPhotonIncidentRead
    cooperPairRecoil := magneticPhotonRecoilRead
    reflectedResponse := magneticPhotonResponseRead
    incidentResponseResidueScaledAt18 :=
      magneticPhotonIncidentResponseResidueScaledAt18
    responseOnLightCone := magneticPhotonResponseOnLightCone
    responseCancelsAppliedField := magneticPhotonResponseCancelsField
    recoilCarriedByCooperPair := magneticPhotonRecoilCarried
    internalMagneticFieldCancelled := maxwellMeissnerInteriorCancelled
    repulsionModeledWithRecoilAndResponse :=
      magneticPhotonRepulsionModeled }

structure ElectromagneticCouplingCalibrationReport where
  name : String
  interpretation : String
  generatedBeforeFirstAlpha : Bool
  coefficientIsGeneratedByTape : Bool
  electricReadAvailable : Bool
  magneticReadAvailable : Bool
  meissnerEffectMeasured : Bool
  appliedMagneticFieldScaledAt18 : Nat
  shieldingQuantumScaledAt18 : Nat
  expulsionQuotient : Nat
  expulsionRemainderScaledAt18 : Nat
  lowerInteger : ElectromagneticCouplingTapeCell
  upperInteger : ElectromagneticCouplingTapeCell
  selectedCell : ElectromagneticCouplingTapeCell
  expelledMagneticFieldScaledAt18 : Nat
  residualInternalFieldScaledAt18 : Nat
  internalMagneticFieldCancelled : Bool
  maxwellSpeedOfLight : MaxwellSpeedOfLightCertificate
  maxwellSpeedOfLightEnforced : Bool
  magneticPhotonExchange : MagneticPhotonExchangeReport
  magneticRepulsionHasRecoilAndResponse : Bool
  tape : ElectromagneticCalibrationTape
  couplingActsByCalibration : Bool
  chargeHorizonOpenedByCoupling : Bool
deriving Repr

def electromagneticCouplingCalibrationReport :
    ElectromagneticCouplingCalibrationReport :=
  { name := "meissner-electromagnetic-coupling-tape"
    interpretation :=
      "measure the electro/magnetic coupling coefficient by expelling the applied magnetic field with Cooper-pair Meissner shielding"
    generatedBeforeFirstAlpha := true
    coefficientIsGeneratedByTape := true
    electricReadAvailable := decide (0 < preAlphaElectricFieldScaledAt18)
    magneticReadAvailable := cavendishMagneticNeedle.deflectsTowardMass
    meissnerEffectMeasured := true
    appliedMagneticFieldScaledAt18 := meissnerAppliedMagneticFieldScaledAt18
    shieldingQuantumScaledAt18 := meissnerShieldingQuantumScaledAt18
    expulsionQuotient := meissnerFluxExpulsionQuotient
    expulsionRemainderScaledAt18 :=
      meissnerFluxExpulsionRemainderScaledAt18
    lowerInteger :=
      electromagneticCouplingTapeCell electromagneticCouplingLowerInteger
    upperInteger :=
      electromagneticCouplingTapeCell electromagneticCouplingUpperInteger
    selectedCell :=
      electromagneticCouplingTapeCell electromagneticCouplingSelected
    expelledMagneticFieldScaledAt18 :=
      meissnerExpelledMagneticFieldScaledAt18
    residualInternalFieldScaledAt18 :=
      meissnerResidualInternalFieldScaledAt18
    internalMagneticFieldCancelled :=
      decide (meissnerResidualInternalFieldScaledAt18 = 0)
    maxwellSpeedOfLight := maxwellSpeedOfLightCertificate
    maxwellSpeedOfLightEnforced := maxwellSpeedOfLightEnforced
    magneticPhotonExchange := magneticPhotonExchangeReport
    magneticRepulsionHasRecoilAndResponse :=
      magneticPhotonRepulsionModeled
    tape := electromagneticCalibrationTape
    couplingActsByCalibration := true
    chargeHorizonOpenedByCoupling := false }

#eval maxwellSpeedOfLightCertificate

#eval magneticPhotonExchangeReport

#eval electromagneticCouplingCalibrationReport

end Measurement
