import Measurement.Meanwhile60

/- MEANWHILE 61 -- COLOR CONTROL, FLAVOR CORRECTION. QED does not give the
electron/Cooper-pair horizon a color charge. Here color is therefore a null
control: if it moves alpha, the measurement leaked through the horizon. Flavor
is the allowed neutrino/exclusion label behind the horizon, read only as the
surface difference between the reader-seeded horizon alpha and the charge-only
alpha.
-/

namespace Measurement

inductive HorizonQEDChannel where
  | flavor
  | colorControl
deriving Repr, DecidableEq

structure HorizonQEDChannelRead where
  channel : HorizonQEDChannel
  residueScaledAt18 : Nat
  lowersAlpha : Bool
  opensHorizon : Bool
  sameFactPreserved : Bool
deriving Repr

def horizonAlphaFlavorResidueScaledAt18 : Nat :=
  if cooperPairHorizonReport.chargeOnlyAlphaScaledAt18 <=
      cooperPairHorizonReport.horizonAlphaScaledAt18 then
    cooperPairHorizonReport.horizonAlphaScaledAt18 -
      cooperPairHorizonReport.chargeOnlyAlphaScaledAt18
  else
    0

def horizonAlphaColorControlResidueScaledAt18 : Nat :=
  0

def horizonFlavorChannelRead : HorizonQEDChannelRead :=
  { channel := .flavor
    residueScaledAt18 := horizonAlphaFlavorResidueScaledAt18
    lowersAlpha := decide (0 < horizonAlphaFlavorResidueScaledAt18)
    opensHorizon := false
    sameFactPreserved := cooperPairHorizonReport.lastNeutrinoSameFact }

def horizonColorControlRead : HorizonQEDChannelRead :=
  { channel := .colorControl
    residueScaledAt18 := horizonAlphaColorControlResidueScaledAt18
    lowersAlpha := false
    opensHorizon := false
    sameFactPreserved := cooperPairHorizonReport.lastNeutrinoSameFact }

def subtractCorrections (value : Nat) (corrections : List Nat) : Nat :=
  corrections.foldl (fun acc correction => acc - correction) value

structure HorizonFlavorColorAlphaReport where
  name : String
  interpretation : String
  readerSeed : Nat
  horizonSameFact : Bool
  horizonInteriorOpened : Bool
  horizonAlphaScaledAt18 : Nat
  horizonInverseAlphaScaledAt18? : Option Nat
  chargeOnlyAlphaScaledAt18 : Nat
  flavorRead : HorizonQEDChannelRead
  colorControlRead : HorizonQEDChannelRead
  colorControlNull : Bool
  totalCorrectionScaledAt18 : Nat
  correctedAlphaScaledAt18 : Nat
  correctedInverseAlphaScaledAt18? : Option Nat
  correctedAlphaLowered : Bool
  correctedMatchesChargeOnly : Bool
  correctionPreservesNeutrinoSameFact : Bool
deriving Repr

def horizonFlavorColorAlphaReport : HorizonFlavorColorAlphaReport :=
  let flavorRead := horizonFlavorChannelRead
  let colorRead := horizonColorControlRead
  let totalCorrection :=
    flavorRead.residueScaledAt18 + colorRead.residueScaledAt18
  let corrected :=
    subtractCorrections cooperPairHorizonReport.horizonAlphaScaledAt18
      [flavorRead.residueScaledAt18, colorRead.residueScaledAt18]
  { name := "horizon-flavor-color-alpha"
    interpretation :=
      "subtract the neutrino/flavor horizon residue while keeping color as a null QED control"
    readerSeed := readerProvidedSeed
    horizonSameFact := cooperPairHorizonReport.lastNeutrinoSameFact
    horizonInteriorOpened := false
    horizonAlphaScaledAt18 := cooperPairHorizonReport.horizonAlphaScaledAt18
    horizonInverseAlphaScaledAt18? :=
      cooperPairHorizonReport.horizonInverseAlphaScaledAt18?
    chargeOnlyAlphaScaledAt18 :=
      cooperPairHorizonReport.chargeOnlyAlphaScaledAt18
    flavorRead := flavorRead
    colorControlRead := colorRead
    colorControlNull := decide (colorRead.residueScaledAt18 = 0)
    totalCorrectionScaledAt18 := totalCorrection
    correctedAlphaScaledAt18 := corrected
    correctedInverseAlphaScaledAt18? := alphaInverseReadScaledAt18? corrected
    correctedAlphaLowered :=
      decide (corrected < cooperPairHorizonReport.horizonAlphaScaledAt18)
    correctedMatchesChargeOnly :=
      decide (corrected = cooperPairHorizonReport.chargeOnlyAlphaScaledAt18)
    correctionPreservesNeutrinoSameFact :=
      cooperPairHorizonReport.lastNeutrinoSameFact &&
        !flavorRead.opensHorizon && !colorRead.opensHorizon }

#eval horizonFlavorColorAlphaReport

end Measurement
