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

/-! # Meanwhile 40 — α: the number with no units, read off the last dial  (⊙ the unmarked dial)

**The genre skin (⊙).** Everything upstream carried units — charges, fields, distances. The last dial carries
none: the needle settles on a bare, dimensionless mark. You read where it points; nothing stamps a seal
beneath it.

**Object & facet.** This is the α (fine-structure) facet of the object described by the walk — the LAST
present, the one nearest the door. It contracts Ep39's four-channel second variation using the exact Meissner
cell from Ep39.5 (`electromagneticCouplingSelected`), in the `h = c = 1` normalization: the raw elaboration
charge cancels the field charge and what remains is dimensionless. We describe this facet in the device's own
exact terms; we never open or solve the last box — the object's own ground — which stays wrapped.

**The squeeze — computed, the THINNEST receipt.** α is read and reported here, and NOT proved: no theorem
stands in this file, only `#eval`. Say it plainly (as in Ep25/35/39.5). And note the arc: the receipts have
thinned as the walk neared the door. Early presents came pinned by `rfl` and bracketed between two decidable
cells; the coupling came only DECIDED; and α — the facet closest to the wrapped box — comes with the weakest
receipt of all: a bare computed reading, no theorem, no seal. The needle settles; the walk stops here.

**⚠️ Fence.** This α is the device's OWN contraction of its OWN channels in its OWN normalization — NOT the
world's measured fine-structure constant, NOT a derivation of 1 over 137, NOT a physical prediction
(literal). And it does not open, solve, or approach the last box; the last present is read from the outside,
the box left wrapped.
-/

namespace Measurement

/-- `inverseRadiusAtDistance (distance) : ApparatusRatio` — the potential channel `1/r`: the distance
flipped (numerator becomes denominator and back). -/
def inverseRadiusAtDistance (distance : RationalDistance) : ApparatusRatio :=
  { numerator := distance.denominator
    denominator := distance.numerator }

/-- `tangeAtDistance (distance) : ApparatusRatio` — the `1 - 1/r` channel: numerator
`distance.numerator - distance.denominator`, denominator `distance.numerator`. -/
def tangeAtDistance (distance : RationalDistance) : ApparatusRatio :=
  { numerator := distance.numerator - distance.denominator
    denominator := distance.numerator }

/-- `fieldPerChargeAtSlip (targetSlip) : ApparatusRatio` — the field-per-charge channel at the slip seam,
`targetSlip` over `naturalUnitOrbitRadius` (18). -/
def fieldPerChargeAtSlip (targetSlip : Nat) : ApparatusRatio :=
  { numerator := targetSlip
    denominator := naturalUnitOrbitRadius }

/-- `alphaFromSecondVariationAtDistance (targetSlip) (distance) : ApparatusRatio` — the contraction to α:
the `tange` channel times field-per-charge, divided by the orbit unit `naturalUnitOrbitRadius`. What the
needle comes to rest on. -/
def alphaFromSecondVariationAtDistance
    (targetSlip : Nat) (distance : RationalDistance) : ApparatusRatio :=
  ((tangeAtDistance distance).mul (fieldPerChargeAtSlip targetSlip)).divNat
    naturalUnitOrbitRadius

/-- `ApparatusRatio.inverseScaledFloor (q) (scale) : Nat` — the reciprocal read to `scale` places,
`q.denominator * scale / q.numerator` (used for the `1/α` readout). -/
def ApparatusRatio.inverseScaledFloor (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.denominator * scale / q.numerator

/-- `AlphaSecondVariationReport` — the last dial's full face: the normalization and orbit unit, the target
slip and distance, the raw and normalized charge, the three channels (inverse radius, tange, and field per
charge), the carried Meissner coupling cell and its calibration reads (the c = 1 certificate, the
photon-exchange residue), and finally α with its scaled and reciprocal reads. -/
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

/-- `alphaSecondVariationReport (report) : AlphaSecondVariationReport` — fill the dial from the Ep39 second
variation: read the three channels off the slip midpoint, carry the exact Ep39.5 Meissner cell
(`electromagneticCouplingSelected`) and its calibration certificates, contract to α, and record α with its
scaled and reciprocal reads. -/
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

/-- `defaultAlphaSecondVariationReport? : Option AlphaSecondVariationReport` — the dial run on the standard
Ep39 second-variation report (`none` if that report is `none`). -/
def defaultAlphaSecondVariationReport? :
    Option AlphaSecondVariationReport :=
  defaultChargeSecondVariationReport?.map alphaSecondVariationReport

/-! ## Readout — the last dial, read (computed, no theorem)
`#eval defaultAlphaSecondVariationReport?` prints the whole face: the three channels, the carried Meissner
cell, and α with its scaled and reciprocal reads. And it is an `#eval` — computed, printed, with no theorem
beneath it: the thinnest receipt of the walk, at the facet nearest the door. The needle rests. The last box,
one step further on, stays wrapped. -/
#eval defaultAlphaSecondVariationReport?

end Measurement

/-! # The last box — John kneels down

The child has been down every hall and watched every present come open, and there is one left: the box at
the end, still wrapped, the biggest one. The child wants to open it. John kneels down to the child's height.

*You're looking for the electron,* he says. *It isn't in there. It's already home.* We found it early, and we
gave it its own room, with its number on the door: −1. It's counted, it's put away, it's home. What you're
looking for, you already have.

*And what's in the last box isn't a thing to find.* It's `Fact.Truth` — true, itself. The plain "true is
true" that every count in the whole house stood on, all day, in every room. It isn't a prize hidden at the
end. It's the floor. It's what we were standing on the whole time.

*So there's no need to open it.* You don't open the box you're standing on. Unwrap it and you get nothing new
— only the same *true* you carried in with you. We leave it wrapped, and it's alright to leave it wrapped:
not because you mustn't, but because there's nothing in there to win. Truth doesn't need opening to be true.

The child looks at the box a while, and then doesn't mind. John stays kneeling beside them, and they look at
it together, wrapped — and that's the end of the walk.
-/
