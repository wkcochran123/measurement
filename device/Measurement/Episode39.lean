import Measurement.Episode38

/- MEANWHILE 39 -- THE FOUR-CHANNEL SECOND VARIATION. The slip charge is not a
single scalar once the apparatus is read locally. It has four simultaneous
coordinates:

  q, normalized q, q/r, q/r^2.

The second variation keeps all four. The ratios below are stored as magnitudes;
the electron sign and orientation are carried alongside them so the same Nat/Nat
apparatus ratios can be reused without losing charge direction.
-/

namespace Measurement

inductive ChargeSecondVariationChannel where
  | rawCharge
  | normalizedCharge
  | potential
  | field
deriving Repr, DecidableEq

structure ChargeSecondVariationComponent where
  channel : ChargeSecondVariationChannel
  magnitude : ApparatusRatio
  scaledAt18 : Nat
  signedUnit : Int
  orientation : ElaborationChargeOrientation
deriving Repr

def rawChargeMagnitudeRatio : ApparatusRatio :=
  { numerator := electronElaborationChargeMagnitude, denominator := 1 }

def normalizedChargeMagnitudeRatio : ApparatusRatio :=
  { numerator := 1, denominator := 1 }

def chargeSecondVariationComponent
    (channel : ChargeSecondVariationChannel)
    (magnitude : ApparatusRatio) : ChargeSecondVariationComponent :=
  { channel := channel
    magnitude := magnitude
    scaledAt18 := magnitude.scaledFloor (pow10 18)
    signedUnit := electronElaborationChargeUnit
    orientation := elaborationChargeOrientationOfSign electronElaborationSignedCharge }

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

def defaultChargeSecondVariationReport? :
    Option ChargeSecondVariationReport :=
  defaultSlipPointChargeReport?.map chargeSecondVariationReport

theorem rawChargeMagnitudeRatio_reads_elaboration_charge :
    rawChargeMagnitudeRatio.numerator = electronElaborationChargeMagnitude ∧
      rawChargeMagnitudeRatio.denominator = 1 := by
  exact ⟨rfl, rfl⟩

#eval defaultChargeSecondVariationReport?

end Measurement
