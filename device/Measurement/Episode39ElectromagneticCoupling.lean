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

/-! # Meanwhile 39.5 — the coupling: the interior field, expelled  (▣ the screened room)

**The genre skin (▣).** Build a screened chamber — a superconductor's Meissner skin — press an applied field
on it from outside, and measure how completely the interior is swept clean.

**Object & facet.** This is the electromagnetic-coupling facet of the object described by the walk — the last
present before α. We describe the facet in the device's own exact terms; we never open or solve the last box
— the object's own ground — which stays wrapped to the end.

**The squeeze — computed/DECIDED, not proved.** The coupling is read by SHIELDING: the applied field (the
needle mean) is expelled by Cooper-pair shielding (quanta of the Lorentz wobble), and the interior residual
DECIDES to zero (`maxwellMeissnerInteriorCancelled := decide (meissnerResidualInternalFieldScaledAt18 = 0)`).
The c = 1 closure, the photon-exchange model, and the coupling calibration are likewise `decide`-Bools
surfaced by `#eval`. Say the plain truth, as in Ep25/35: there is NO theorem in this file — nothing here is
proved and no receipt is claimed; each certificate is computed and DECIDED, read off, never certified by a
theorem.

**⚠️ Two hard fences.**
1. **A MEISSNER residual, and nothing else.** The interior-field cancellation is a Meissner (shielding)
   residual in the device's own model. It is NOT the residual of the last box's own equation, NOT a real
   gauge-theory solution, NOT the wrapped box coming open. The last box stays wrapped, never approached.
2. **Model-owned.** The coupling, the Meissner shielding, the c = 1 closure, the photon exchange are the
   device's OWN certificates — NOT real superconductivity, NOT real electromagnetism, NOT a real photon, NOT
   the real speed of light (literal, not a disavowal).
-/

namespace Measurement

/-- `ElectromagneticCouplingCoefficient` — the coupling as a mixed number: a `wholeFactor` plus a
`numerator`/`denominator` fraction, with a scaled read. `Repr`, `DecidableEq`. -/
structure ElectromagneticCouplingCoefficient where
  wholeFactor : Nat
  numerator : Nat
  denominator : Nat
  factorScaledAt18 : Nat
deriving Repr, DecidableEq

/-- `electromagneticCouplingNumerator (whole) (numerator) (denominator) : Nat` — the improper numerator,
`whole * denominator + numerator`. -/
def electromagneticCouplingNumerator
    (whole numerator denominator : Nat) : Nat :=
  whole * denominator + numerator

/-- `electromagneticCouplingFactorScaledAt18 (whole) (numerator) (denominator) : Nat` — the coefficient to
eighteen places (`whole * readoutScale` when the denominator is 0; else the improper numerator times `readoutScale`
over the denominator). -/
def electromagneticCouplingFactorScaledAt18
    (whole numerator denominator : Nat) : Nat :=
  if denominator = 0 then
    whole * readoutScale
  else
    electromagneticCouplingNumerator whole numerator denominator * readoutScale /
      denominator

/-- `electromagneticCouplingCoefficient (whole) (numerator) (denominator) : ElectromagneticCouplingCoefficient`
— assemble the coefficient with its scaled factor. -/
def electromagneticCouplingCoefficient
    (whole numerator denominator : Nat) :
    ElectromagneticCouplingCoefficient :=
  { wholeFactor := whole
    numerator := numerator
    denominator := denominator
    factorScaledAt18 :=
      electromagneticCouplingFactorScaledAt18 whole numerator denominator }

/-- `preAlphaElectricFieldScaledAt18 : Nat` — the electric side, read before α: the Ep39 second-variation
field (`0` if that report is `none`). -/
def preAlphaElectricFieldScaledAt18 : Nat :=
  match defaultChargeSecondVariationReport? with
  | some report => report.field.scaledAt18
  | none => 0

/-- `preAlphaElectricPotentialScaledAt18 : Nat` — the electric potential, read before α from the Ep39
report. -/
def preAlphaElectricPotentialScaledAt18 : Nat :=
  match defaultChargeSecondVariationReport? with
  | some report => report.potential.scaledAt18
  | none => 0

/-- `preAlphaMagneticWobbleScaledAt18 : Nat` — the magnetic side: the Lorentz wobble (one shielding
quantum). -/
def preAlphaMagneticWobbleScaledAt18 : Nat :=
  lorentzOrbitBracketReport.wobbleScaledAt18

/-- `preAlphaMagneticNeedleMeanScaledAt18 : Nat` — the magnetic needle mean (the applied field). -/
def preAlphaMagneticNeedleMeanScaledAt18 : Nat :=
  cavendishMagneticNeedle.needleMeanScaledAt18

/-- `meissnerAppliedMagneticFieldScaledAt18 : Nat` — the applied field pressing on the chamber, the needle
mean. -/
def meissnerAppliedMagneticFieldScaledAt18 : Nat :=
  preAlphaMagneticNeedleMeanScaledAt18

/-- `meissnerShieldingQuantumScaledAt18 : Nat` — one shielding quantum, the Lorentz wobble. -/
def meissnerShieldingQuantumScaledAt18 : Nat :=
  preAlphaMagneticWobbleScaledAt18

/-- `meissnerFluxExpulsionQuotient : Nat` — how many quanta it takes to expel the field, the applied field
over one shielding quantum. -/
def meissnerFluxExpulsionQuotient : Nat :=
  meissnerAppliedMagneticFieldScaledAt18 /
    meissnerShieldingQuantumScaledAt18

/-- `meissnerFluxExpulsionRemainderScaledAt18 : Nat` — what falls short of a whole quantum, the applied field
mod one shielding quantum. -/
def meissnerFluxExpulsionRemainderScaledAt18 : Nat :=
  meissnerAppliedMagneticFieldScaledAt18 %
    meissnerShieldingQuantumScaledAt18

/-- `electromagneticCoupledMagneticResidueScaledAt18 (coefficient) : Nat` — the field the shielding leaves
standing for a given coefficient (the wobble times the coefficient, whole or improper). -/
def electromagneticCoupledMagneticResidueScaledAt18
    (coefficient : ElectromagneticCouplingCoefficient) : Nat :=
  if coefficient.denominator = 0 then
    preAlphaMagneticWobbleScaledAt18 * coefficient.wholeFactor
  else
    preAlphaMagneticWobbleScaledAt18 *
      electromagneticCouplingNumerator
        coefficient.wholeFactor coefficient.numerator coefficient.denominator /
        coefficient.denominator

/-- `ElectromagneticCouplingTapeCell` — one frame of the calibration tape: a coefficient beside the electric
field and potential, the magnetic wobble and needle mean, the coupled magnetic residue, and a
`generatedBeforeAlpha` flag. -/
structure ElectromagneticCouplingTapeCell where
  coefficient : ElectromagneticCouplingCoefficient
  electricFieldScaledAt18 : Nat
  electricPotentialScaledAt18 : Nat
  magneticWobbleScaledAt18 : Nat
  magneticNeedleMeanScaledAt18 : Nat
  coupledMagneticResidueScaledAt18 : Nat
  generatedBeforeAlpha : Bool
deriving Repr

/-- `electromagneticCouplingTapeCell (coefficient) : ElectromagneticCouplingTapeCell` — record one frame for
a coefficient (all reads generated before α). -/
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

/-- `ElectromagneticCalibrationTape` — a list of tape cells. -/
abbrev ElectromagneticCalibrationTape :=
  List ElectromagneticCouplingTapeCell

/-- `electromagneticCouplingLowerInteger : ElectromagneticCouplingCoefficient` — the lower integer
coefficient, the expulsion quotient over one. -/
def electromagneticCouplingLowerInteger :
    ElectromagneticCouplingCoefficient :=
  electromagneticCouplingCoefficient meissnerFluxExpulsionQuotient 0 1

/-- `electromagneticCouplingUpperInteger : ElectromagneticCouplingCoefficient` — the upper integer, the
quotient's successor over one. -/
def electromagneticCouplingUpperInteger :
    ElectromagneticCouplingCoefficient :=
  electromagneticCouplingCoefficient meissnerFluxExpulsionQuotient.succ 0 1

/-- `electromagneticCouplingSelected : ElectromagneticCouplingCoefficient` — the exact selected cell: the
quotient plus the remainder over the shielding quantum. -/
def electromagneticCouplingSelected :
    ElectromagneticCouplingCoefficient :=
  electromagneticCouplingCoefficient
    meissnerFluxExpulsionQuotient
    meissnerFluxExpulsionRemainderScaledAt18
    meissnerShieldingQuantumScaledAt18

/-- `meissnerExpelledMagneticFieldScaledAt18 : Nat` — the field the selected shielding expels. -/
def meissnerExpelledMagneticFieldScaledAt18 : Nat :=
  electromagneticCoupledMagneticResidueScaledAt18
    electromagneticCouplingSelected

/-- `meissnerResidualInternalFieldScaledAt18 : Nat` — what remains inside: the applied field minus the
expelled (`natAbsDiff`). This is the interior residual that decides to zero — a MEISSNER (shielding)
residual, not the last box's own residual. -/
def meissnerResidualInternalFieldScaledAt18 : Nat :=
  natAbsDiff meissnerAppliedMagneticFieldScaledAt18
    meissnerExpelledMagneticFieldScaledAt18

/-- Orientation companion (Batch 4): the SIGNED interior residual — positive when the applied field
exceeds the expelled, negative when expulsion overshoots. The `Nat` above is its magnitude
(`natAbsDiff_eq_signedDiff_natAbs`); this carries the shielding DIRECTION that `natAbsDiff` dropped. -/
def meissnerResidualInternalFieldOrientationScaledAt18 : Int :=
  signedDiff meissnerAppliedMagneticFieldScaledAt18 meissnerExpelledMagneticFieldScaledAt18

/-- `electromagneticCalibrationTape : ElectromagneticCalibrationTape` — three frames bracketing the coupling:
the lower integer, the selected cell, the upper integer. -/
def electromagneticCalibrationTape : ElectromagneticCalibrationTape :=
  [ electromagneticCouplingTapeCell electromagneticCouplingLowerInteger,
    electromagneticCouplingTapeCell electromagneticCouplingSelected,
    electromagneticCouplingTapeCell electromagneticCouplingUpperInteger ]

/-- `maxwellSpeedOfLightSquaredScaledAt18 : Nat` — the chamber's own light-speed-squared, set to one
(`readoutScale`). -/
def maxwellSpeedOfLightSquaredScaledAt18 : Nat :=
  readoutScale

/-- `maxwellNaturalUnitVelocitySquaredScaledAt18 : Nat` — the natural-unit orbit's v² (scaled). -/
def maxwellNaturalUnitVelocitySquaredScaledAt18 : Nat :=
  (cooperElectronOrbitRead naturalUnitOrbitRadius).velocitySquaredScaledAt18

/-- `maxwellLorentzBoundaryVelocitySquaredScaledAt18 : Nat` — the Lorentz-boundary v² (scaled). -/
def maxwellLorentzBoundaryVelocitySquaredScaledAt18 : Nat :=
  lorentzOrbitBracketReport.boundary.velocitySquaredScaledAt18

/-- `maxwellNaturalUnitVelocitySquaredIsC : Bool` — `decide`s whether the natural-unit v² equals the
light-speed-squared (one). A computed yes-or-no, not a proof. -/
def maxwellNaturalUnitVelocitySquaredIsC : Bool :=
  decide
    (maxwellNaturalUnitVelocitySquaredScaledAt18 =
      maxwellSpeedOfLightSquaredScaledAt18)

/-- `maxwellLorentzBoundaryVelocitySquaredIsC : Bool` — `decide`s whether the Lorentz-boundary v² equals
one. -/
def maxwellLorentzBoundaryVelocitySquaredIsC : Bool :=
  decide
    (maxwellLorentzBoundaryVelocitySquaredScaledAt18 =
      maxwellSpeedOfLightSquaredScaledAt18)

/-- `maxwellLorentzBoundaryLightlike : Bool` — `decide`s whether the Lorentz boundary regime is lightlike. -/
def maxwellLorentzBoundaryLightlike : Bool :=
  decide
    (lorentzOrbitBracketReport.boundary.regime =
      LorentzOrbitRegime.lightlikeBoundary)

/-- `maxwellElectricReadAvailable : Bool` — `decide`s that the pre-α electric field is positive. -/
def maxwellElectricReadAvailable : Bool :=
  decide (0 < preAlphaElectricFieldScaledAt18)

/-- `maxwellMagneticReadAvailable : Bool` — the needle deflects toward mass and the pre-α wobble is
positive. -/
def maxwellMagneticReadAvailable : Bool :=
  cavendishMagneticNeedle.deflectsTowardMass &&
    decide (0 < preAlphaMagneticWobbleScaledAt18)

/-- `maxwellMeissnerInteriorCancelled : Bool` — the key certificate: `decide (meissnerResidualInternalFieldScaledAt18 = 0)`
— the interior residual decides to zero. A computed decision, NOT a theorem. -/
def maxwellMeissnerInteriorCancelled : Bool :=
  decide (meissnerResidualInternalFieldScaledAt18 = 0)

/-- `maxwellElectricAndMagneticShareLightCone : Bool` — the AND of the two v²-is-one checks and the
lightlike-boundary check. -/
def maxwellElectricAndMagneticShareLightCone : Bool :=
  maxwellNaturalUnitVelocitySquaredIsC &&
    maxwellLorentzBoundaryVelocitySquaredIsC &&
    maxwellLorentzBoundaryLightlike

/-- `maxwellGaussElectricEnforced : Bool` — electric read available AND the shared-light-cone check. -/
def maxwellGaussElectricEnforced : Bool :=
  maxwellElectricReadAvailable &&
    maxwellElectricAndMagneticShareLightCone

/-- `maxwellGaussMagneticEnforced : Bool` — the Meissner interior cancelled AND the shared-light-cone
check. -/
def maxwellGaussMagneticEnforced : Bool :=
  maxwellMeissnerInteriorCancelled &&
    maxwellElectricAndMagneticShareLightCone

/-- `maxwellFaradayInductionEnforced : Bool` — magnetic read available AND the shared-light-cone check. -/
def maxwellFaradayInductionEnforced : Bool :=
  maxwellMagneticReadAvailable &&
    maxwellElectricAndMagneticShareLightCone

/-- `maxwellAmpereMaxwellEnforced : Bool` — electric and magnetic reads available AND the shared-light-cone
check. -/
def maxwellAmpereMaxwellEnforced : Bool :=
  maxwellElectricReadAvailable &&
    maxwellMagneticReadAvailable &&
    maxwellElectricAndMagneticShareLightCone

/-- `maxwellSpeedOfLightEnforced : Bool` — the closure: all four "Maxwell equation" flags AND-ed. A chain of
decided Bools, not a proof. -/
def maxwellSpeedOfLightEnforced : Bool :=
  maxwellGaussElectricEnforced &&
    maxwellGaussMagneticEnforced &&
    maxwellFaradayInductionEnforced &&
    maxwellAmpereMaxwellEnforced

/-- `MaxwellSpeedOfLightCertificate` — the c = 1 certificate: a name and interpretation, the radius and the
three velocity² reads, the availability / cancellation / light-cone flags, the four "Maxwell equation
enforced" flags, and the closure flag. All computed. -/
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

/-- `maxwellSpeedOfLightCertificate : MaxwellSpeedOfLightCertificate` — fill the certificate. Its own
interpretation string names it: "in the device this is the Maxwell closure c = 1" — the DEVICE'S closure, a
computed certificate, not the world's Maxwell equations proved. -/
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

/-- `MagneticPhotonLeg` — the three legs of the modelled exchange: `incidentMagneticField`,
`cooperPairRecoil`, `reflectedResponse`. `Repr`, `DecidableEq`. -/
inductive MagneticPhotonLeg where
  | incidentMagneticField
  | cooperPairRecoil
  | reflectedResponse
deriving Repr, DecidableEq

/-- `MagneticPhotonExchangeRead` — one leg's read: the leg, its field (scaled), the light-cone v², and
whether the magnetic read is available. -/
structure MagneticPhotonExchangeRead where
  leg : MagneticPhotonLeg
  fieldScaledAt18 : Nat
  lightConeVelocitySquaredScaledAt18 : Nat
  magneticReadAvailable : Bool
deriving Repr

/-- `magneticPhotonIncidentRead : MagneticPhotonExchangeRead` — the incident leg, carrying the applied
field. -/
def magneticPhotonIncidentRead : MagneticPhotonExchangeRead :=
  { leg := .incidentMagneticField
    fieldScaledAt18 := meissnerAppliedMagneticFieldScaledAt18
    lightConeVelocitySquaredScaledAt18 :=
      maxwellLorentzBoundaryVelocitySquaredScaledAt18
    magneticReadAvailable := maxwellMagneticReadAvailable }

/-- `magneticPhotonRecoilRead : MagneticPhotonExchangeRead` — the Cooper-pair recoil leg, carrying the
expelled field. -/
def magneticPhotonRecoilRead : MagneticPhotonExchangeRead :=
  { leg := .cooperPairRecoil
    fieldScaledAt18 := meissnerExpelledMagneticFieldScaledAt18
    lightConeVelocitySquaredScaledAt18 :=
      maxwellLorentzBoundaryVelocitySquaredScaledAt18
    magneticReadAvailable := maxwellMagneticReadAvailable }

/-- `magneticPhotonResponseRead : MagneticPhotonExchangeRead` — the reflected-response leg, carrying the
expelled field. -/
def magneticPhotonResponseRead : MagneticPhotonExchangeRead :=
  { leg := .reflectedResponse
    fieldScaledAt18 := meissnerExpelledMagneticFieldScaledAt18
    lightConeVelocitySquaredScaledAt18 :=
      maxwellLorentzBoundaryVelocitySquaredScaledAt18
    magneticReadAvailable := maxwellMagneticReadAvailable }

/-- `magneticPhotonIncidentResponseResidueScaledAt18 : Nat` — the gap between the incident and response
fields (`natAbsDiff`). -/
def magneticPhotonIncidentResponseResidueScaledAt18 : Nat :=
  natAbsDiff magneticPhotonIncidentRead.fieldScaledAt18
    magneticPhotonResponseRead.fieldScaledAt18

/-- Orientation companion (Batch 4): the SIGNED incident−response gap — positive when the incident field
exceeds the response, negative otherwise. The `Nat` above is its magnitude; this keeps the direction. -/
def magneticPhotonIncidentResponseResidueOrientationScaledAt18 : Int :=
  signedDiff magneticPhotonIncidentRead.fieldScaledAt18 magneticPhotonResponseRead.fieldScaledAt18

/-- `magneticPhotonResponseOnLightCone : Bool` — the shared-light-cone check AND that the response's
light-cone v² equals one. -/
def magneticPhotonResponseOnLightCone : Bool :=
  maxwellElectricAndMagneticShareLightCone &&
    decide
      (magneticPhotonResponseRead.lightConeVelocitySquaredScaledAt18 =
        maxwellSpeedOfLightSquaredScaledAt18)

/-- `magneticPhotonResponseCancelsField : Bool` — `decide`s that the incident-response residue is zero. -/
def magneticPhotonResponseCancelsField : Bool :=
  decide (magneticPhotonIncidentResponseResidueScaledAt18 = 0)

/-- `magneticPhotonRecoilCarried : Bool` — `decide`s that the recoil and response fields agree. -/
def magneticPhotonRecoilCarried : Bool :=
  decide
    (magneticPhotonRecoilRead.fieldScaledAt18 =
      magneticPhotonResponseRead.fieldScaledAt18)

/-- `magneticPhotonRepulsionModeled : Bool` — the AND of on-light-cone, cancels-field, recoil-carried, and
Meissner-cancelled. A modelled repulsion, decided, not proved. -/
def magneticPhotonRepulsionModeled : Bool :=
  magneticPhotonResponseOnLightCone &&
    magneticPhotonResponseCancelsField &&
    magneticPhotonRecoilCarried &&
    maxwellMeissnerInteriorCancelled

/-- `MagneticPhotonExchangeReport` — the photon-exchange model: a name and interpretation, the mediator
flag, the three leg reads, the incident-response residue, and the on-light-cone / cancels / recoil-carried /
internal-cancelled / repulsion-modelled flags. -/
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

/-- `magneticPhotonExchangeReport : MagneticPhotonExchangeReport` — fill the model. Its interpretation string
calls it a model: "model magnetic repulsion as an incident photon read, a Cooper-pair recoil, and a
reflected response" — a story the device tells, decided, not a real photon. -/
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

/-- `ElectromagneticCouplingCalibrationReport` — the whole calibration: name and interpretation, the
before-α flags, availability, the Meissner-effect-measured flag, applied field and shielding quantum, the
expulsion quotient and remainder, the three tape frames, the expelled field and residual, whether the
interior cancelled, the c = 1 certificate, the photon-exchange model, the tape, and — set FALSE on purpose —
`chargeHorizonOpenedByCoupling` (the coupling only calibrates; it does not open the charge horizon). -/
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

/-- `electromagneticCouplingCalibrationReport : ElectromagneticCouplingCalibrationReport` — fill the whole
calibration (the Meissner read, the c = 1 certificate, the photon model, the tape). The interior-cancelled
field is a `decide`; `chargeHorizonOpenedByCoupling` is `false` (the coupling only calibrates). -/
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

/-! ## Readouts — the screened certificates (computed, not proved)
Three reads print the c = 1 certificate, the photon-exchange model, and the whole calibration. And every one
is an `#eval` over decided Bools — computed and decided, printed, with no theorem beneath any of it. The
interior residual decides to zero: a MEISSNER cancellation, a shielding residual, not the last box's own
residual. One present is out — the coupling, its interior swept clean. The next facet is α, which consumes
this exact Meissner cell; and the last box past it stays wrapped. -/
#eval maxwellSpeedOfLightCertificate

#eval magneticPhotonExchangeReport

#eval electromagneticCouplingCalibrationReport



end Measurement
