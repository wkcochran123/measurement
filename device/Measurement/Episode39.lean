import Measurement.Episode38

/- MEANWHILE 39 -- THE FOUR-CHANNEL SECOND VARIATION. The slip charge is not a
single scalar once the apparatus is read locally. It has four simultaneous
coordinates:

  q, normalized q, q/r, q/r^2.

The second variation keeps all four. The ratios below are stored as magnitudes;
the electron sign and orientation are carried alongside them so the same Nat/Nat
apparatus ratios can be reused without losing charge direction.
-/

/-! # Meanwhile 39 — the second variation: the charge, bent into a curve  (⌒ shipwright's fairing batten)

**The genre skin (⌒).** A shipwright springs a flexible batten through control points to draw a fair curve.
Read the slip charge locally and it stops being one bare number: it springs into a curve.

**Object & facet.** This is the charge-read-a-curvature-shaped-way, across four channels, facet of the
object Yang–Mills describes. We describe the facet in the device's own exact terms; we never open or solve
Yang–Mills, and the last box stays wrapped.

**The squeeze (a PINNED equality).** Lay a batten through four control points — the raw charge, the charge
normalized, the charge over distance (potential), and over distance squared (field) — and the batten takes
a fair curve through them all, kept to second order (`variationRank = 2`, the curvature). And the raw
control point still lands on the elaboration charge exactly: `rawChargeMagnitudeRatio.numerator =
electronElaborationChargeMagnitude ∧ rawChargeMagnitudeRatio.denominator = 1`, by `⟨rfl, rfl⟩`. Even bent
into a curve, the charge is pinned to the same number.

**⚠️ Fence.** This "second variation" / "curvature" is the SHAPE of a batten we sprung through OUR own four
channels — NOT real spacetime curvature, NOT general relativity, NOT a real gravitational field bending
(literal). The charge is still Ep37's elaboration cost under our own sign convention; reading it a
curvature-shaped way does not upgrade it to a world quantity.
-/

namespace Measurement

/-- `ChargeSecondVariationChannel` — the four control points the batten passes through: `rawCharge`,
`normalizedCharge`, `potential`, `field`. `Repr`, `DecidableEq`. -/
inductive ChargeSecondVariationChannel where
  | rawCharge
  | normalizedCharge
  | potential
  | field
deriving Repr, DecidableEq

/-- `ChargeSecondVariationComponent` — what sits at one control point: its `channel`, its `magnitude` (as an
`ApparatusRatio`) and scaled read, and — carried alongside so the plain `Nat`/`Nat` ratios keep their
direction — the electron's `signedUnit` and `orientation`. -/
structure ChargeSecondVariationComponent where
  channel : ChargeSecondVariationChannel
  magnitude : ApparatusRatio
  scaledAt18 : Nat
  signedUnit : Int
  orientation : ElaborationChargeOrientation
deriving Repr

/-- `rawChargeMagnitudeRatio : ApparatusRatio` — the raw charge as a whole number over one — the elaboration
charge magnitude itself (`numerator = electronElaborationChargeMagnitude`, `denominator = 1`). -/
def rawChargeMagnitudeRatio : ApparatusRatio :=
  { numerator := electronElaborationChargeMagnitude, denominator := 1 }

/-- `normalizedChargeMagnitudeRatio : ApparatusRatio` — the same charge normalized, one over one. -/
def normalizedChargeMagnitudeRatio : ApparatusRatio :=
  { numerator := 1, denominator := 1 }

/-- `chargeSecondVariationComponent (channel) (magnitude) : ChargeSecondVariationComponent` — set a
magnitude at a control point and pin the electron's sign and orientation to it. -/
def chargeSecondVariationComponent
    (channel : ChargeSecondVariationChannel)
    (magnitude : ApparatusRatio) : ChargeSecondVariationComponent :=
  { channel := channel
    magnitude := magnitude
    scaledAt18 := magnitude.scaledFloor (pow10 18)
    signedUnit := electronElaborationChargeUnit
    orientation := elaborationChargeOrientationOfSign electronElaborationSignedCharge }

/-- `chargeSecondVariationComponents (report) : List ChargeSecondVariationComponent` — lay all four points:
raw, normalized, potential, and field (potential and field read off the Ep38 slip-point report). The batten
through every point. -/
def chargeSecondVariationComponents
    (report : SlipPointChargeReport) : List ChargeSecondVariationComponent :=
  [ chargeSecondVariationComponent
      .rawCharge rawChargeMagnitudeRatio,
    chargeSecondVariationComponent
      .normalizedCharge normalizedChargeMagnitudeRatio,
    chargeSecondVariationComponent
      .potential report.midpointPotentialMagnitude,
    chargeSecondVariationComponent
      .field report.exactBoundaryFieldMagnitude ]

/-- `ChargeSecondVariationReport` — the whole fair curve: the normalization it is drawn in, the variation
rank (2, the curvature), the slip-point report it rests on, the four control points, and their count. -/
structure ChargeSecondVariationReport where
  normalization : String
  variationRank : Nat
  slipPoint : SlipPointChargeReport
  rawCharge : ChargeSecondVariationComponent
  normalizedCharge : ChargeSecondVariationComponent
  potential : ChargeSecondVariationComponent
  field : ChargeSecondVariationComponent
  components : List ChargeSecondVariationComponent
  componentCount : Nat
deriving Repr

/-- `chargeSecondVariationReport (report) : ChargeSecondVariationReport` — spring the batten from a
slip-point report: build the four components and gather them (normalization `h = c = 1`, rank 2). -/
def chargeSecondVariationReport
    (report : SlipPointChargeReport) : ChargeSecondVariationReport :=
  let raw :=
    chargeSecondVariationComponent
      .rawCharge rawChargeMagnitudeRatio
  let normalized :=
    chargeSecondVariationComponent
      .normalizedCharge normalizedChargeMagnitudeRatio
  let potential :=
    chargeSecondVariationComponent
      .potential report.midpointPotentialMagnitude
  let field :=
    chargeSecondVariationComponent
      .field report.exactBoundaryFieldMagnitude
  let components := [raw, normalized, potential, field]
  { normalization := "h = c = 1"
    variationRank := 2
    slipPoint := report
    rawCharge := raw
    normalizedCharge := normalized
    potential := potential
    field := field
    components := components
    componentCount := components.length }

/-- `defaultChargeSecondVariationReport? : Option ChargeSecondVariationReport` — the batten run on the
standard Ep38 slip-point report (`none` if that report is `none`). -/
def defaultChargeSecondVariationReport? :
    Option ChargeSecondVariationReport :=
  defaultSlipPointChargeReport?.map chargeSecondVariationReport

/-- `rawChargeMagnitudeRatio_reads_elaboration_charge`.
**Proposition:** `rawChargeMagnitudeRatio.numerator = electronElaborationChargeMagnitude ∧
rawChargeMagnitudeRatio.denominator = 1` — the raw control point is the elaboration charge magnitude over
one.
**Mechanism:** `⟨rfl, rfl⟩` — both conjuncts by `rfl`, kernel-computed.
**Squeeze role:** even bent into a curve across four channels, the raw point is pinned to the elaboration
charge — the same number, read a curvature-shaped way, not a real curvature and not a real charge. -/
theorem rawChargeMagnitudeRatio_reads_elaboration_charge :
    rawChargeMagnitudeRatio.numerator = electronElaborationChargeMagnitude ∧
      rawChargeMagnitudeRatio.denominator = 1 := by
  exact ⟨rfl, rfl⟩

/-! ## Readout — the faired curve
`#eval defaultChargeSecondVariationReport?` prints the whole curve: the four control points, the
normalization, and the rank. The theorem above pins the raw point to the elaboration charge. The next facet,
the coupling, is next door. -/
#eval defaultChargeSecondVariationReport?

end Measurement
