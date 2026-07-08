import Measurement.Meanwhile57

set_option maxRecDepth 4096

/- MEANWHILE 58 -- SEED THE ELECTRON. A random electron should not be built by
expanding a huge unary `Number`. The seed enters in two places:

  * a bounded corridor index, `seededElectronIndex`, so the electron has a
    charge/mass/value face without allocating an enormous numeral;
  * the orbit-carry PRNG seed, so the alpha study walks a different sequence of
    rational neighborhoods and therefore reads a different number.

The default apparatus remains deterministic. Operators can supply any seed to
`seededElectronAlphaMeasurementReport`.
-/

namespace Measurement

def seededInitialOrbitCarryState
    (seed latticeDenominator : Nat) : OrbitCarryState :=
  { initialOrbitCarryState latticeDenominator with seed := seed }

def seededElectronIndex (seed : Nat) : Nat :=
  CooperManual.nextSeed seed % corridorPeriod

def seededElectron (seed : Nat) : Electron :=
  electronFromIndex (seededElectronIndex seed)

def seededElectronFace (seed : Nat) : CorridorFace :=
  electronCorridorFace (seededElectron seed)

def seededElectronAlphaStudyInitialState
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (seed : Nat) : OrbitCarryState :=
  orbitCarryRun aperture read electronCompletedTurns
    (seededInitialOrbitCarryState seed aperture.latticePeriod)

def seededElectronAlphaRichardsonStudyPoint
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (seed trialCount : Nat) : ElectronAlphaRichardsonStudyPoint :=
  let initialState := seededElectronAlphaStudyInitialState aperture read seed
  let point :=
    neutrinoAlphaRichardsonStudyPointFromState aperture read initialState
      trialCount
  { trialCount := point.trialCount
    formalStudyDepth := point.formalStudyDepth
    chargeFaceSamples := point.chargeFaceSamples
    massFaceSamples := point.massFaceSamples
    valueFaceSamples := point.valueFaceSamples
    finalSeed := point.finalSeed
    finalResidueNumerator := point.finalResidueNumerator
    alphaSumScaledAt18 := point.alphaSumScaledAt18
    sampleAlphaMeanScaledAt18 := point.sampleAlphaMeanScaledAt18
    sampleAlphaVarianceScaledAt36 := point.sampleAlphaVarianceScaledAt36 }

def seededElectronAlphaRichardsonReport
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (corridor : OrbitCorridorReport)
    (seed coarse middle fine : Nat) : ElectronAlphaRichardsonReport :=
  let coarseStudy :=
    seededElectronAlphaRichardsonStudyPoint aperture read seed coarse
  let middleStudy :=
    seededElectronAlphaRichardsonStudyPoint aperture read seed middle
  let fineStudy :=
    seededElectronAlphaRichardsonStudyPoint aperture read seed fine
  let firstSlip := electronAlphaRichardsonSlip coarseStudy middleStudy
  let secondSlip := electronAlphaRichardsonSlip middleStudy fineStudy
  let bracketLower :=
    natBracketLower firstSlip.richardsonAlphaScaledAt18
      secondSlip.richardsonAlphaScaledAt18
  let bracketUpper :=
    natBracketUpper firstSlip.richardsonAlphaScaledAt18
      secondSlip.richardsonAlphaScaledAt18
  let sourceAlpha :=
    (electronAlphaFromChargeSquared
      aperture.targetElementaryChargeSquared).scaledFloor (pow10 18)
  let midpoint := (bracketLower + bracketUpper) / 2
  { name := "seeded-electron-alpha-richardson"
    normalization := "h = c = 1"
    refinementRatio := 2
    richardsonOrder := 1
    sourceAlphaScaledAt18 := sourceAlpha
    studies := [coarseStudy, middleStudy, fineStudy]
    firstSlip := firstSlip
    secondSlip := secondSlip
    orbitSlipBrackets := corridor.slipReads
    richardsonBracketLowerScaledAt18 := bracketLower
    richardsonBracketUpperScaledAt18 := bracketUpper
    richardsonBracketWidthScaledAt18 := bracketUpper - bracketLower
    signedSlipsBracketZero :=
      signedValuesBracketZero firstSlip.signedMeanSlipScaledAt18
        secondSlip.signedMeanSlipScaledAt18
    fineStudyMeanInsideRichardsonBracket :=
      natWithinBracket bracketLower fineStudy.sampleAlphaMeanScaledAt18
        bracketUpper
    richardsonAlphaEstimateScaledAt18 := midpoint
    estimateSourceAbsDiffScaledAt18 := natAbsDiff midpoint sourceAlpha }

structure SeededElectronAlphaMeasurementReport where
  name : String
  seed : Nat
  seededElectronIndex : Nat
  seededElectronFace : CorridorFace
  studyInitialSeed : Nat
  firstStudyDrawModuloThree : Nat
  firstStudyDrawFace : CorridorFace
  coarseTrials : Nat
  middleTrials : Nat
  fineTrials : Nat
  seededAlphaScaledAt18 : Nat
  seededInverseAlphaScaledAt18? : Option Nat
  defaultMeasuredAlphaScaledAt18 : Nat
  differsFromDefaultMeasurement : Bool
  seededSourceAbsDiffScaledAt18 : Nat
  seededBracketLowerScaledAt18 : Nat
  seededBracketUpperScaledAt18 : Nat
  seededBracketWidthScaledAt18 : Nat
  seededAlphaInsideBracket : Bool
  chargeFaceSamples : Nat
  massFaceSamples : Nat
  valueFaceSamples : Nat
  finalSeed : Nat
  finalResidueNumerator : Nat
deriving Repr

def seededElectronAlphaMeasurementReport
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (corridor : OrbitCorridorReport)
    (defaultAlpha : AlphaMeasurementReport)
    (seed coarse middle fine : Nat) :
    SeededElectronAlphaMeasurementReport :=
  let initialState := seededElectronAlphaStudyInitialState aperture read seed
  let firstDraw := chooseNeighborhoodFace initialState.seed
  let report :=
    seededElectronAlphaRichardsonReport aperture read corridor seed coarse
      middle fine
  let fineStudy :=
    seededElectronAlphaRichardsonStudyPoint aperture read seed fine
  { name := "seeded-electron-alpha-measurement"
    seed := seed
    seededElectronIndex := seededElectronIndex seed
    seededElectronFace := seededElectronFace seed
    studyInitialSeed := initialState.seed
    firstStudyDrawModuloThree := firstDraw.2 % 3
    firstStudyDrawFace := firstDraw.1
    coarseTrials := coarse
    middleTrials := middle
    fineTrials := fine
    seededAlphaScaledAt18 := report.richardsonAlphaEstimateScaledAt18
    seededInverseAlphaScaledAt18? :=
      alphaInverseReadScaledAt18? report.richardsonAlphaEstimateScaledAt18
    defaultMeasuredAlphaScaledAt18 := defaultAlpha.measuredAlphaScaledAt18
    differsFromDefaultMeasurement :=
      decide (report.richardsonAlphaEstimateScaledAt18 ≠
        defaultAlpha.measuredAlphaScaledAt18)
    seededSourceAbsDiffScaledAt18 := report.estimateSourceAbsDiffScaledAt18
    seededBracketLowerScaledAt18 := report.richardsonBracketLowerScaledAt18
    seededBracketUpperScaledAt18 := report.richardsonBracketUpperScaledAt18
    seededBracketWidthScaledAt18 := report.richardsonBracketWidthScaledAt18
    seededAlphaInsideBracket :=
      natWithinBracket report.richardsonBracketLowerScaledAt18
        report.richardsonAlphaEstimateScaledAt18
        report.richardsonBracketUpperScaledAt18
    chargeFaceSamples := fineStudy.chargeFaceSamples
    massFaceSamples := fineStudy.massFaceSamples
    valueFaceSamples := fineStudy.valueFaceSamples
    finalSeed := fineStudy.finalSeed
    finalResidueNumerator := fineStudy.finalResidueNumerator }

def readerProvidedSeed : Nat :=
  109383671947

def defaultSeededElectronAlphaMeasurementReport? :
    Option SeededElectronAlphaMeasurementReport :=
  match defaultAdjacentWobbleReport?, defaultOrbitCorridorReport?,
    defaultAlphaMeasurementReport? with
  | some aperture, some corridor, some defaultAlpha =>
      some
        (seededElectronAlphaMeasurementReport aperture
          cavendishChargeMassNormalization corridor defaultAlpha
          readerProvidedSeed 1000 2000 4000)
  | _, _, _ => none

#eval defaultSeededElectronAlphaMeasurementReport?

end Measurement
