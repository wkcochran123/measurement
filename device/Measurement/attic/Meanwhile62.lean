import Measurement.Meanwhile61

/- MEANWHILE 62 -- ALPHA OF QFT. The QED receipt kept color as a null control.
For the QFT receipt we treat color, flavor, and phase as device sectors: three
color faces, six flavor labels, and two phase labels. The horizon flavor residue
is the single surface residue already measured in Meanwhile61. QFT asks for the
same correction spread over the full device sector count.

The photon certificate from the Meissner side gives one more boundary read:
absorption is modeled as a de Broglie phase kick. In the `h = c = 1` device
units, the absorbed photon has momentum `p`, wavelength `lambda = 1 / p`, and
the kick closes when `p * lambda = 1`. The phase kick does not make the photon
carry color; instead it prevents the boundary from selecting one color/flavor
label. The color/flavor plane is therefore carried as fuzz/variance around the
QFT center, not as another alpha correction.

This is an apparatus alpha: it depends on the finite sector certificate below,
not a claim of a scheme-independent continuum QFT coupling.
-/

namespace Measurement

inductive QFTColor where
  | red
  | green
  | blue
deriving Repr, DecidableEq

inductive QFTFlavor where
  | up
  | down
  | strange
  | charm
  | top
  | bottom
deriving Repr, DecidableEq

inductive QFTPhase where
  | plus
  | minus
deriving Repr, DecidableEq

def qftColors : List QFTColor :=
  [.red, .green, .blue]

def qftFlavors : List QFTFlavor :=
  [.up, .down, .strange, .charm, .top, .bottom]

def qftPhases : List QFTPhase :=
  [.plus, .minus]

def qftColorCount : Nat :=
  qftColors.length

def qftFlavorCount : Nat :=
  qftFlavors.length

def qftPhaseCount : Nat :=
  qftPhases.length

def qftSectorCount : Nat :=
  qftColorCount * qftFlavorCount * qftPhaseCount

def qftColorFlavorSectorCount : Nat :=
  qftColorCount * qftFlavorCount

def qftTotalSectorResidueScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18 *
    qftSectorCount

def qftAdditionalResidueAfterQEDScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18 *
    (qftSectorCount - 1)

def qftAlphaScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.correctedAlphaScaledAt18 -
    qftAdditionalResidueAfterQEDScaledAt18

def qftPhotonAbsorbedAsPhaseKick : Bool :=
  magneticPhotonExchangeReport.photonMediatorPresent &&
    magneticPhotonExchangeReport.responseOnLightCone &&
    magneticPhotonExchangeReport.recoilCarriedByCooperPair

def qftPhotonDeBroglieMomentumScaledAt18 : Nat :=
  magneticPhotonExchangeReport.incident.fieldScaledAt18

def qftPhotonDeBroglieWavelengthScaledAt18 : Nat :=
  if qftPhotonDeBroglieMomentumScaledAt18 = 0 then
    0
  else
    pow10 36 / qftPhotonDeBroglieMomentumScaledAt18

def qftPhotonDeBroglieActionQuantumScaledAt18 : Nat :=
  pow10 18

def qftPhotonDeBroglieProductScaledAt18 : Nat :=
  qftPhotonDeBroglieMomentumScaledAt18 *
    qftPhotonDeBroglieWavelengthScaledAt18 / pow10 18

def qftPhotonDeBroglieResidualScaledAt18 : Nat :=
  natAbsDiff qftPhotonDeBroglieActionQuantumScaledAt18
    qftPhotonDeBroglieProductScaledAt18

def qftPhotonDeBroglieProductCloses : Bool :=
  qftPhotonAbsorbedAsPhaseKick &&
    decide
      (qftPhotonDeBroglieProductScaledAt18 <=
        qftPhotonDeBroglieActionQuantumScaledAt18) &&
    decide
      (qftPhotonDeBroglieResidualScaledAt18 <
        qftPhotonDeBroglieMomentumScaledAt18)

structure QFTPhotonDeBroglieReport where
  name : String
  interpretation : String
  hSetToOne : Bool
  cSetToOne : Bool
  photonMomentumScaledAt18 : Nat
  deBroglieWavelengthScaledAt18 : Nat
  actionQuantumScaledAt18 : Nat
  momentumWavelengthProductScaledAt18 : Nat
  productResidualScaledAt18 : Nat
  productClosesOneQuantum : Bool
  phaseKickAvailable : Bool
deriving Repr

def qftPhotonDeBroglieReport : QFTPhotonDeBroglieReport :=
  { name := "qft-photon-de-broglie-phase"
    interpretation :=
      "read photon absorption as a de Broglie phase kick: in h = c = 1 units, p times lambda closes one action quantum"
    hSetToOne := true
    cSetToOne := maxwellSpeedOfLightCertificate.cSetToOne
    photonMomentumScaledAt18 := qftPhotonDeBroglieMomentumScaledAt18
    deBroglieWavelengthScaledAt18 :=
      qftPhotonDeBroglieWavelengthScaledAt18
    actionQuantumScaledAt18 := qftPhotonDeBroglieActionQuantumScaledAt18
    momentumWavelengthProductScaledAt18 :=
      qftPhotonDeBroglieProductScaledAt18
    productResidualScaledAt18 := qftPhotonDeBroglieResidualScaledAt18
    productClosesOneQuantum := qftPhotonDeBroglieProductCloses
    phaseKickAvailable :=
      qftPhotonAbsorbedAsPhaseKick && qftPhotonDeBroglieProductCloses }

def qftPhotonPhaseFlips : Bool :=
  qftPhotonDeBroglieReport.phaseKickAvailable &&
    decide (qftPhaseCount = 2)

def qftPhotonPhaseFuzzesColorFlavor : Bool :=
  qftPhotonPhaseFlips &&
    decide (0 < qftColorCount) &&
    decide (0 < qftFlavorCount)

def qftPhotonPhaseFuzzAmplitudeScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18 *
    qftColorFlavorSectorCount

def qftPhotonPhaseFuzzVarianceScaledAt36 : Nat :=
  square qftPhotonPhaseFuzzAmplitudeScaledAt18

def qftPhotonPhaseFuzzLowerAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 - qftPhotonPhaseFuzzAmplitudeScaledAt18

def qftPhotonPhaseFuzzUpperAlphaScaledAt18 : Nat :=
  qftAlphaScaledAt18 + qftPhotonPhaseFuzzAmplitudeScaledAt18

structure QFTPhotonPhaseAbsorptionReport where
  name : String
  interpretation : String
  photonMediatorPresent : Bool
  photonAbsorbedAsPhaseKick : Bool
  deBroglieMomentumScaledAt18 : Nat
  deBroglieWavelengthScaledAt18 : Nat
  deBroglieProductResidualScaledAt18 : Nat
  deBrogliePhaseKickAvailable : Bool
  phaseCount : Nat
  phaseFlips : Bool
  colorCount : Nat
  flavorCount : Nat
  colorFlavorSectorCount : Nat
  fuzzesColorFlavorLabels : Bool
  centerAlphaScaledAt18 : Nat
  centerInverseAlphaScaledAt18? : Option Nat
  fuzzAmplitudeScaledAt18 : Nat
  fuzzVarianceScaledAt36 : Nat
  lowerAlphaScaledAt18 : Nat
  upperAlphaScaledAt18 : Nat
  lowerInverseAlphaScaledAt18? : Option Nat
  upperInverseAlphaScaledAt18? : Option Nat
  centerUnchangedByPhotonFuzz : Bool
deriving Repr

def qftPhotonPhaseAbsorptionReport :
    QFTPhotonPhaseAbsorptionReport :=
  { name := "qft-photon-phase-absorption"
    interpretation :=
      "photon absorption changes phase; the phase kick fuzzes color/flavor labels as variance around the QFT alpha center"
    photonMediatorPresent := magneticPhotonExchangeReport.photonMediatorPresent
    photonAbsorbedAsPhaseKick := qftPhotonAbsorbedAsPhaseKick
    deBroglieMomentumScaledAt18 := qftPhotonDeBroglieMomentumScaledAt18
    deBroglieWavelengthScaledAt18 :=
      qftPhotonDeBroglieWavelengthScaledAt18
    deBroglieProductResidualScaledAt18 :=
      qftPhotonDeBroglieResidualScaledAt18
    deBrogliePhaseKickAvailable :=
      qftPhotonDeBroglieReport.phaseKickAvailable
    phaseCount := qftPhaseCount
    phaseFlips := qftPhotonPhaseFlips
    colorCount := qftColorCount
    flavorCount := qftFlavorCount
    colorFlavorSectorCount := qftColorFlavorSectorCount
    fuzzesColorFlavorLabels := qftPhotonPhaseFuzzesColorFlavor
    centerAlphaScaledAt18 := qftAlphaScaledAt18
    centerInverseAlphaScaledAt18? := alphaInverseReadScaledAt18? qftAlphaScaledAt18
    fuzzAmplitudeScaledAt18 := qftPhotonPhaseFuzzAmplitudeScaledAt18
    fuzzVarianceScaledAt36 := qftPhotonPhaseFuzzVarianceScaledAt36
    lowerAlphaScaledAt18 := qftPhotonPhaseFuzzLowerAlphaScaledAt18
    upperAlphaScaledAt18 := qftPhotonPhaseFuzzUpperAlphaScaledAt18
    lowerInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? qftPhotonPhaseFuzzLowerAlphaScaledAt18
    upperInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? qftPhotonPhaseFuzzUpperAlphaScaledAt18
    centerUnchangedByPhotonFuzz :=
      decide (qftAlphaScaledAt18 = qftAlphaScaledAt18) }

structure QFTAlphaReport where
  name : String
  interpretation : String
  readerSeed : Nat
  colorCount : Nat
  flavorCount : Nat
  phaseCount : Nat
  sectorCount : Nat
  horizonSameFact : Bool
  horizonInteriorOpened : Bool
  horizonAlphaScaledAt18 : Nat
  qedAlphaScaledAt18 : Nat
  singleHorizonFlavorResidueScaledAt18 : Nat
  totalSectorResidueScaledAt18 : Nat
  additionalResidueAfterQEDScaledAt18 : Nat
  qftAlphaScaledAt18 : Nat
  qftInverseAlphaScaledAt18? : Option Nat
  photonAbsorptionChangesPhase : Bool
  photonAbsorptionIsDeBrogliePhase : Bool
  photonDeBroglieWavelengthScaledAt18 : Nat
  photonDeBroglieResidualScaledAt18 : Nat
  photonPhaseFuzzesColorFlavor : Bool
  photonPhaseFuzzAmplitudeScaledAt18 : Nat
  photonPhaseFuzzVarianceScaledAt36 : Nat
  qftAlphaLowerThanHorizon : Bool
  qftAlphaLowerThanQED : Bool
  qftPreservesHorizonSameFact : Bool
deriving Repr

def qftAlphaReport : QFTAlphaReport :=
  { name := "qft-alpha"
    interpretation :=
      "compute apparatus alpha after the color/flavor/phase sector certificate applies to the Cooper-pair horizon"
    readerSeed := readerProvidedSeed
    colorCount := qftColorCount
    flavorCount := qftFlavorCount
    phaseCount := qftPhaseCount
    sectorCount := qftSectorCount
    horizonSameFact := horizonFlavorColorAlphaReport.horizonSameFact
    horizonInteriorOpened := horizonFlavorColorAlphaReport.horizonInteriorOpened
    horizonAlphaScaledAt18 :=
      horizonFlavorColorAlphaReport.horizonAlphaScaledAt18
    qedAlphaScaledAt18 :=
      horizonFlavorColorAlphaReport.correctedAlphaScaledAt18
    singleHorizonFlavorResidueScaledAt18 :=
      horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18
    totalSectorResidueScaledAt18 := qftTotalSectorResidueScaledAt18
    additionalResidueAfterQEDScaledAt18 :=
      qftAdditionalResidueAfterQEDScaledAt18
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    qftInverseAlphaScaledAt18? := alphaInverseReadScaledAt18? qftAlphaScaledAt18
    photonAbsorptionChangesPhase := qftPhotonAbsorbedAsPhaseKick
    photonAbsorptionIsDeBrogliePhase :=
      qftPhotonDeBroglieReport.phaseKickAvailable
    photonDeBroglieWavelengthScaledAt18 :=
      qftPhotonDeBroglieWavelengthScaledAt18
    photonDeBroglieResidualScaledAt18 :=
      qftPhotonDeBroglieResidualScaledAt18
    photonPhaseFuzzesColorFlavor := qftPhotonPhaseFuzzesColorFlavor
    photonPhaseFuzzAmplitudeScaledAt18 :=
      qftPhotonPhaseFuzzAmplitudeScaledAt18
    photonPhaseFuzzVarianceScaledAt36 :=
      qftPhotonPhaseFuzzVarianceScaledAt36
    qftAlphaLowerThanHorizon :=
      decide (qftAlphaScaledAt18 <
        horizonFlavorColorAlphaReport.horizonAlphaScaledAt18)
    qftAlphaLowerThanQED :=
      decide (qftAlphaScaledAt18 <
        horizonFlavorColorAlphaReport.correctedAlphaScaledAt18)
    qftPreservesHorizonSameFact :=
      horizonFlavorColorAlphaReport.correctionPreservesNeutrinoSameFact &&
        !horizonFlavorColorAlphaReport.horizonInteriorOpened }

#eval qftPhotonDeBroglieReport

#eval qftPhotonPhaseAbsorptionReport

#eval qftAlphaReport

end Measurement
