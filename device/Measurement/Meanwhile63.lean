import Measurement.Meanwhile62

/- MEANWHILE 63 -- EVALUATE THE MASS NOISE. Once the Cooper-pair horizon is
charge only, the gravity channel is no longer hidden inside the quotient. It is
a separate electron tug on the "doesn't matter" Cooper pair.

This file records that tug as mass noise. It does not subtract the mass read
from alpha by default; it brackets the QFT alpha by the observed tug residue and
reports the wobble variance already present in the carried electron study.
-/

namespace Measurement

def natListMax : List Nat -> Nat
  | [] => 0
  | value :: rest => rest.foldl Nat.max value

def natListMin : List Nat -> Nat
  | [] => 0
  | value :: rest => rest.foldl Nat.min value

def natRawVariance (values : List Nat) : Nat :=
  match values.length with
  | 0 => 0
  | count =>
      let mean := meanNatFloor values
      values.foldl
        (fun sum value => sum + square (natAbsDiff value mean)) 0 / count

def ratioScaledAt18? (numerator denominator : Nat) : Option Nat :=
  if denominator = 0 then
    none
  else
    some (numerator * pow10 18 / denominator)

def qftNoiseHeartbeatSamples : List Nat :=
  eventHorizonStudyExecutionReport.executionReads.map
    fun read => read.heartbeat

def qftNoiseHeartbeatMean : Nat :=
  meanNatFloor qftNoiseHeartbeatSamples

def qftNoiseHeartbeatMin : Nat :=
  natListMin qftNoiseHeartbeatSamples

def qftNoiseHeartbeatMax : Nat :=
  natListMax qftNoiseHeartbeatSamples

def qftNoiseHeartbeatSpan : Nat :=
  qftNoiseHeartbeatMax - qftNoiseHeartbeatMin

def qftNoiseHeartbeatVarianceRaw : Nat :=
  natRawVariance qftNoiseHeartbeatSamples

def readerSeededFineStudyNoise? : Option ElectronAlphaRichardsonStudyPoint :=
  match defaultAdjacentWobbleReport? with
  | some aperture =>
      some
        (seededElectronAlphaRichardsonStudyPoint aperture
          cavendishChargeMassNormalization readerProvidedSeed 4000)
  | none => none

def readerSeededFineAlphaVarianceScaledAt36 : Nat :=
  match readerSeededFineStudyNoise? with
  | some study => study.sampleAlphaVarianceScaledAt36
  | none => 0

def defaultAlphaWobbleVarianceScaledAt36 : Nat :=
  match defaultElectronAlphaStudyReport? with
  | some report => report.sampleAlphaVarianceScaledAt36
  | none => 0

def qftTugNoiseScaledAt18 : Nat :=
  cooperPairHorizonReport.electronTugRead.gravityTugResidueScaledAt18

def qftMassNoiseScaledAt18 : Nat :=
  qftTugNoiseScaledAt18

def qftAlphaNoiseLowerScaledAt18 : Nat :=
  qftAlphaScaledAt18 - qftTugNoiseScaledAt18

def qftAlphaNoiseUpperScaledAt18 : Nat :=
  qftAlphaScaledAt18 + qftTugNoiseScaledAt18

structure QFTNoiseReport where
  name : String
  interpretation : String
  horizonContainsGravity : Bool
  tugAffectsChargeHorizon : Bool
  noiseInterpretedAsMass : Bool
  qftAlphaScaledAt18 : Nat
  qftAlphaNoiseLowerScaledAt18 : Nat
  qftAlphaNoiseUpperScaledAt18 : Nat
  qftAlphaNoiseWidthScaledAt18 : Nat
  qftAlphaLowerInverseScaledAt18? : Option Nat
  qftAlphaUpperInverseScaledAt18? : Option Nat
  tugNoiseResidueScaledAt18 : Nat
  massNoiseResidueScaledAt18 : Nat
  tugNoiseFractionOfQFTAlphaScaledAt18? : Option Nat
  tugNoiseFractionOfFlavorResidueScaledAt18? : Option Nat
  tugNoiseFractionOfQFTSectorResidueScaledAt18? : Option Nat
  tugNoiseBelowFlavorResidue : Bool
  tugNoiseBelowQFTSectorResidue : Bool
  tugNoiseBelowQFTAlpha : Bool
  heartbeatSamples : List Nat
  heartbeatMean : Nat
  heartbeatMin : Nat
  heartbeatMax : Nat
  heartbeatSpan : Nat
  heartbeatVarianceRaw : Nat
  defaultAlphaWobbleVarianceScaledAt36 : Nat
  readerSeededFineAlphaVarianceScaledAt36 : Nat
deriving Repr

def qftNoiseReport : QFTNoiseReport :=
  { name := "qft-noise"
    interpretation :=
      "evaluate external gravity/tug noise as mass after the Cooper-pair horizon is restricted to charge"
    horizonContainsGravity := cooperPairHorizonReport.horizonContainsGravity
    tugAffectsChargeHorizon :=
      cooperPairHorizonReport.electronTugRead.affectsChargeHorizon
    noiseInterpretedAsMass := true
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    qftAlphaNoiseLowerScaledAt18 := qftAlphaNoiseLowerScaledAt18
    qftAlphaNoiseUpperScaledAt18 := qftAlphaNoiseUpperScaledAt18
    qftAlphaNoiseWidthScaledAt18 :=
      qftAlphaNoiseUpperScaledAt18 - qftAlphaNoiseLowerScaledAt18
    qftAlphaLowerInverseScaledAt18? :=
      alphaInverseReadScaledAt18? qftAlphaNoiseUpperScaledAt18
    qftAlphaUpperInverseScaledAt18? :=
      alphaInverseReadScaledAt18? qftAlphaNoiseLowerScaledAt18
    tugNoiseResidueScaledAt18 := qftTugNoiseScaledAt18
    massNoiseResidueScaledAt18 := qftMassNoiseScaledAt18
    tugNoiseFractionOfQFTAlphaScaledAt18? :=
      ratioScaledAt18? qftTugNoiseScaledAt18 qftAlphaScaledAt18
    tugNoiseFractionOfFlavorResidueScaledAt18? :=
      ratioScaledAt18? qftTugNoiseScaledAt18
        horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18
    tugNoiseFractionOfQFTSectorResidueScaledAt18? :=
      ratioScaledAt18? qftTugNoiseScaledAt18
        qftTotalSectorResidueScaledAt18
    tugNoiseBelowFlavorResidue :=
      decide (qftTugNoiseScaledAt18 <
        horizonFlavorColorAlphaReport.flavorRead.residueScaledAt18)
    tugNoiseBelowQFTSectorResidue :=
      decide (qftTugNoiseScaledAt18 < qftTotalSectorResidueScaledAt18)
    tugNoiseBelowQFTAlpha :=
      decide (qftTugNoiseScaledAt18 < qftAlphaScaledAt18)
    heartbeatSamples := qftNoiseHeartbeatSamples
    heartbeatMean := qftNoiseHeartbeatMean
    heartbeatMin := qftNoiseHeartbeatMin
    heartbeatMax := qftNoiseHeartbeatMax
    heartbeatSpan := qftNoiseHeartbeatSpan
    heartbeatVarianceRaw := qftNoiseHeartbeatVarianceRaw
    defaultAlphaWobbleVarianceScaledAt36 :=
      defaultAlphaWobbleVarianceScaledAt36
    readerSeededFineAlphaVarianceScaledAt36 :=
      readerSeededFineAlphaVarianceScaledAt36 }

#eval qftNoiseReport

end Measurement
