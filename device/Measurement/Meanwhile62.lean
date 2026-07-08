import Measurement.Meanwhile61

/- MEANWHILE 62 -- ALPHA OF QFT. The QED receipt kept color as a null control.
For the QFT receipt we treat color, flavor, and phase as device sectors: three
color faces, six flavor labels, and two phase labels. The horizon flavor residue
is the single surface residue already measured in Meanwhile61. QFT asks for the
same correction spread over the full device sector count.

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

def qftTotalSectorResidueScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18 *
    qftSectorCount

def qftAdditionalResidueAfterQEDScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18 *
    (qftSectorCount - 1)

def qftAlphaScaledAt18 : Nat :=
  horizonFlavorColorAlphaReport.correctedAlphaScaledAt18 -
    qftAdditionalResidueAfterQEDScaledAt18

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
    qftAlphaLowerThanHorizon :=
      decide (qftAlphaScaledAt18 <
        horizonFlavorColorAlphaReport.horizonAlphaScaledAt18)
    qftAlphaLowerThanQED :=
      decide (qftAlphaScaledAt18 <
        horizonFlavorColorAlphaReport.correctedAlphaScaledAt18)
    qftPreservesHorizonSameFact :=
      horizonFlavorColorAlphaReport.correctionPreservesNeutrinoSameFact &&
        !horizonFlavorColorAlphaReport.horizonInteriorOpened }

#eval qftAlphaReport

end Measurement
