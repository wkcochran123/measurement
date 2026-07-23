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

/-! ### Projective totalization (Batch 2, Kodo GATE) — extend `ApparatusRatio` to the projective points so
a degenerate can NEVER masquerade as a real value. A genuine reading is `n/d` with `d > 0`; the two
projective points are `0/0` (INDETERMINATE) and `n/0`, `n > 0` (the point at INFINITY). Both are distinct
from the genuine zero `0/d`, `d > 0`. On the reading domain (d ∈ [17/9, 2], α ≠ 0) nothing degenerate is
ever produced, so these are OFF-DOMAIN markers — they exist only to keep a degenerate honest, never silent. -/
def ApparatusRatio.isIndeterminate (q : ApparatusRatio) : Bool :=
  q.numerator == 0 && q.denominator == 0
def ApparatusRatio.isAtInfinity (q : ApparatusRatio) : Bool :=
  q.denominator == 0 && q.numerator != 0
/-- `ApparatusRatio.reciprocal (q)` — the projective-total reciprocal: swap `num`/`den`. It sends the
genuine zero `0/d ↦ d/0` (the point at INFINITY) and `n/0 ↦ 0/n`; an involution on the projective line.
This is where the `1/α` pole becomes the explicit `n/0` marker instead of a silent `/0 → 0`. -/
def ApparatusRatio.reciprocal (q : ApparatusRatio) : ApparatusRatio :=
  { numerator := q.denominator, denominator := q.numerator }

/-- `tangeAtDistance (distance) : ApparatusRatio` — the `1 - 1/r` channel, `(num − den)/num = 1 − 1/d`.
TOTALIZED (Batch 2): on the reading domain `d ≥ 1` (`den ≤ num`) it is the exact `(num−den)/num`
(byte-identical to before). For `d < 1` the true `1 − 1/d < 0` is unrepresentable in a `Nat` ratio, so
instead of the old silent `Nat`-truncated `0` (which masqueraded as the genuine `d = 1` zero) it returns
the projective INDETERMINATE `0/0` — distinct and off-domain (never reached: reads sit at `d ∈ [17/9, 2]`). -/
def tangeAtDistance (distance : RationalDistance) : ApparatusRatio :=
  if distance.denominator ≤ distance.numerator then
    { numerator := distance.numerator - distance.denominator
      denominator := distance.numerator }
  else
    { numerator := 0, denominator := 0 }   -- projective indeterminate (d < 1, off-domain)

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

/-- `ApparatusRatio.inverseScaledFloor (q) (scale) : Nat` — the `1/α` read to `scale` places. TOTALIZED
(Batch 2): routed through the projective `reciprocal` (`q.reciprocal.scaledFloor scale`), which is
`q.denominator * scale / q.numerator` — BYTE-IDENTICAL to before on every input (see
`inverseScaledFloor_eq`). The gain: the `α = 0` pole now flows through the explicit `n/0` marker
(`q.reciprocal.isAtInfinity`), so a consumer can detect the pole instead of reading a silent `/0 → 0`. -/
def ApparatusRatio.inverseScaledFloor (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.reciprocal.scaledFloor scale

/-- `ApparatusRatio.inverseScaledRemainder (q) (scale) : Nat` — the sub-scale tail, via the projective
reciprocal (`q.reciprocal.scaledRemainder scale = q.denominator * scale % q.numerator`, byte-identical).
Kept alongside so the `1/α` readout is information-preserving; `inverseScaledFloor`'s value is unchanged. -/
def ApparatusRatio.inverseScaledRemainder (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.reciprocal.scaledRemainder scale

/-! ### Totalization certificates (Batch 2) — the projective sentinels are distinct, and ON-DOMAIN the
totalized reads are BYTE-IDENTICAL to the originals (the jar-neutrality proof: nothing the device reads
moved). All choice-free. -/

-- BYTE-IDENTICAL (rfl): the reciprocal-routed inverse reads equal the original formulas on EVERY input.
theorem inverseScaledFloor_eq (q : ApparatusRatio) (scale : Nat) :
    q.inverseScaledFloor scale = q.denominator * scale / q.numerator := rfl
theorem inverseScaledRemainder_eq (q : ApparatusRatio) (scale : Nat) :
    q.inverseScaledRemainder scale = q.denominator * scale % q.numerator := rfl

-- ON-DOMAIN (d ≥ 1): tange is exactly the raw `(num−den)/num` — no distortion where the device reads.
theorem tangeAtDistance_on_domain (distance : RationalDistance)
    (h : distance.denominator ≤ distance.numerator) :
    tangeAtDistance distance =
      { numerator := distance.numerator - distance.denominator, denominator := distance.numerator } := by
  simp [tangeAtDistance, h]

-- OFF-DOMAIN (d < 1): tange is the projective INDETERMINATE, distinguished from a genuine zero.
theorem tangeAtDistance_off_domain (distance : RationalDistance)
    (h : distance.numerator < distance.denominator) :
    (tangeAtDistance distance).isIndeterminate = true := by
  simp [tangeAtDistance, Nat.not_le.mpr h, ApparatusRatio.isIndeterminate]

-- SENTINEL DISTINCTNESS: the two projective points are distinct from a genuine zero 0/d (d>0).
example : ({ numerator := 0, denominator := 0 } : ApparatusRatio).isIndeterminate = true := by decide
example : ({ numerator := 5, denominator := 0 } : ApparatusRatio).isAtInfinity = true := by decide
example : ({ numerator := 0, denominator := 1 } : ApparatusRatio).isIndeterminate = false
    ∧ ({ numerator := 0, denominator := 1 } : ApparatusRatio).isAtInfinity = false := by decide
-- the α=0 pole reciprocal is the n/0 point at infinity, NOT a genuine zero:
example : (({ numerator := 0, denominator := 7 } : ApparatusRatio).reciprocal).isAtInfinity = true := by decide
#print axioms inverseScaledFloor_eq
#print axioms tangeAtDistance_on_domain

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
    distanceScaledAt18 := distance.scaledFloor (readoutScale)
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
    alphaScaledAt18 := alpha.scaledFloor (readoutScale)
    inverseAlphaScaledAt18 := alpha.inverseScaledFloor (readoutScale) }

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
