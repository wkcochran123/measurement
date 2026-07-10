import Measurement.Meanwhile51

set_option maxRecDepth 4096

/- MEANWHILE 52 -- THE NEUTRINO SLOT. The anti-Cooper-pair channel is the
spin-up/spin-down antimatter pair. The neutrino-shaped object is the electron
residue against that channel: the electron is present, but the anti-pair
absorption channel is not occupied. We crank that residual channel three times,
then run the alpha/Richardson study again from the cranked state.
-/

namespace Measurement

inductive Spin
  | up
  | down
deriving Repr, DecidableEq

inductive MatterOrientation
  | matter
  | antimatter
deriving Repr, DecidableEq

structure PairMember where
  orientation : MatterOrientation
  spin : Spin
deriving Repr

structure CooperPairChannel where
  left : PairMember
  right : PairMember
  spinBalanced : Bool
  chargeOrientationBalanced : Bool
deriving Repr

def antiCooperPairChannel : CooperPairChannel :=
  { left := { orientation := .antimatter, spin := .up }
    right := { orientation := .antimatter, spin := .down }
    spinBalanced := true
    chargeOrientationBalanced := true }

def antiCooperPairChannelOpenBool : Bool :=
  antiCooperPairChannel.spinBalanced &&
    antiCooperPairChannel.chargeOrientationBalanced

def antiCooperPairOccupiedBool : Bool :=
  false

def antiCooperPairTruth : Prop :=
  antiCooperPairOccupiedBool = true

namespace Fact

def ANTI_COOPER_PAIR : Fact :=
  { truth := antiCooperPairTruth
    decTruth :=
      show Decidable (antiCooperPairOccupiedBool = true) from
        if h : antiCooperPairOccupiedBool = true then
          isTrue h
        else
          isFalse h }

end Fact

def neutrinoResidueTruthBool : Bool :=
  electronCorridorTruthBool && !antiCooperPairOccupiedBool

def neutrinoResidueTruth : Prop :=
  neutrinoResidueTruthBool = true

namespace Fact

def NEUTRINO : Fact :=
  { truth := neutrinoResidueTruth
    decTruth :=
      show Decidable (neutrinoResidueTruthBool = true) from
        if h : neutrinoResidueTruthBool = true then
          isTrue h
        else
          isFalse h }

end Fact

def neutrinoNumberFromNat : Nat -> Number
  | 0 => .zero Fact.NEUTRINO
  | n + 1 => .one Fact.NEUTRINO (neutrinoNumberFromNat n)

def neutrinoFormalStudyAux : Nat -> Study -> Study
  | 0, study => study
  | fuel + 1, study =>
      neutrinoFormalStudyAux fuel
        (.data Fact.NEUTRINO electronAlphaStudyTrial study)

def neutrinoFormalStudy (trialCount : Nat) : Study :=
  neutrinoFormalStudyAux trialCount (.hypothesis Fact.NEUTRINO)

def alphaStudyRunFromState
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (initialState : OrbitCarryState)
    (trialCount : Nat) : ElectronAlphaStudyAccumulator :=
  (List.range trialCount).foldl (electronAlphaStudyFold aperture read)
    { index := 0
      state := initialState
      samples := [] }

def neutrinoCrankState
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (crankCount : Nat) : OrbitCarryState :=
  orbitCarryRun aperture read crankCount
    (electronAlphaStudyInitialState aperture read)

def neutrinoCrankStateAfterThree
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport) : OrbitCarryState :=
  neutrinoCrankState aperture read 3

def neutrinoAlphaStudyReportFromState
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (initialState : OrbitCarryState)
    (trialCount : Nat) : ElectronAlphaStudyReport :=
  let run := alphaStudyRunFromState aperture read initialState trialCount
  let alphaSamples := run.samples.map fun sample => sample.alphaScaledAt18
  let sourceAlpha :=
    electronAlphaFromChargeSquared aperture.targetElementaryChargeSquared
  let sourceAlphaScaledAt18 := sourceAlpha.scaledFloor (pow10 18)
  let sampleMean := meanNatFloor alphaSamples
  { name := "neutrino-cranked-alpha-study"
    normalization := "h = c = 1"
    cSetToOne := true
    startsFromElectronState := true
    startingCompletedTurns := initialState.steps
    trialCount := trialCount
    formalStudyDepth := studyDataCount (neutrinoFormalStudy trialCount)
    initialSeed := initialState.seed
    finalSeed := run.state.seed
    initialResidueNumerator := initialState.carriedResidueNumerator
    finalResidueNumerator := run.state.carriedResidueNumerator
    chargeFaceSamples := electronAlphaStudyFaceCount run.samples .charge
    massFaceSamples := electronAlphaStudyFaceCount run.samples .mass
    valueFaceSamples := electronAlphaStudyFaceCount run.samples .value
    sourceAlphaScaledAt18 := sourceAlphaScaledAt18
    meanSourceAbsDiffScaledAt18 :=
      natAbsDiff sampleMean sourceAlphaScaledAt18
    sampleAlphaMeanScaledAt18 := sampleMean
    sampleMeanInverseAlphaScaledAt18? :=
      ratioInverseScaledFloor?
        { numerator := sampleMean, denominator := pow10 18 } (pow10 18)
    sampleAlphaVarianceScaledAt18 := varianceNatScaledAt18 alphaSamples
    sampleAlphaVarianceScaledAt36 := varianceNatScaledAt36 alphaSamples
    firstFiveSamples := run.samples.take 5
    lastFiveSamples := run.samples.drop (run.samples.length - 5) }

structure NeutrinoAlphaRichardsonStudyPoint where
  trialCount : Nat
  formalStudyDepth : Nat
  chargeFaceSamples : Nat
  massFaceSamples : Nat
  valueFaceSamples : Nat
  finalSeed : Nat
  finalResidueNumerator : Nat
  alphaSumScaledAt18 : Nat
  sampleAlphaMeanScaledAt18 : Nat
  sampleAlphaVarianceScaledAt36 : Nat
deriving Repr

def neutrinoAlphaRichardsonStudyPointFromState
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (initialState : OrbitCarryState)
    (trialCount : Nat) : NeutrinoAlphaRichardsonStudyPoint :=
  let acc :=
    (List.range trialCount).foldl
      (electronAlphaRichardsonStudyFold aperture read)
      { index := 0
        state := initialState
        chargeFaceSamples := 0
        massFaceSamples := 0
        valueFaceSamples := 0
        alphaSumScaledAt18 := 0
        alphaSquareSumScaledAt36 := 0 }
  let mean :=
    match trialCount with
    | 0 => 0
    | count => acc.alphaSumScaledAt18 / count
  { trialCount := trialCount
    formalStudyDepth := trialCount
    chargeFaceSamples := acc.chargeFaceSamples
    massFaceSamples := acc.massFaceSamples
    valueFaceSamples := acc.valueFaceSamples
    finalSeed := acc.state.seed
    finalResidueNumerator := acc.state.carriedResidueNumerator
    alphaSumScaledAt18 := acc.alphaSumScaledAt18
    sampleAlphaMeanScaledAt18 := mean
    sampleAlphaVarianceScaledAt36 :=
      varianceFromSumScaledAt36 trialCount acc.alphaSumScaledAt18
        acc.alphaSquareSumScaledAt36 mean }

def neutrinoRichardsonSlip
    (lower upper : NeutrinoAlphaRichardsonStudyPoint) :
    ElectronAlphaRichardsonSlip :=
  { lowerTrialCount := lower.trialCount
    upperTrialCount := upper.trialCount
    lowerMeanAlphaScaledAt18 := lower.sampleAlphaMeanScaledAt18
    upperMeanAlphaScaledAt18 := upper.sampleAlphaMeanScaledAt18
    signedMeanSlipScaledAt18 :=
      signedScaledDelta lower.sampleAlphaMeanScaledAt18
        upper.sampleAlphaMeanScaledAt18
    absoluteMeanSlipScaledAt18 :=
      natAbsDiff lower.sampleAlphaMeanScaledAt18
        upper.sampleAlphaMeanScaledAt18
    richardsonAlphaScaledAt18 :=
      richardsonOrderOneScaledAt18 lower.sampleAlphaMeanScaledAt18
        upper.sampleAlphaMeanScaledAt18 }

structure NeutrinoAlphaRichardsonReport where
  name : String
  normalization : String
  crankCount : Nat
  sourceAlphaScaledAt18 : Nat
  studies : List NeutrinoAlphaRichardsonStudyPoint
  firstSlip : ElectronAlphaRichardsonSlip
  secondSlip : ElectronAlphaRichardsonSlip
  richardsonBracketLowerScaledAt18 : Nat
  richardsonBracketUpperScaledAt18 : Nat
  richardsonBracketWidthScaledAt18 : Nat
  signedSlipsBracketZero : Bool
  sourceAlphaInsideRichardsonBracket : Bool
  richardsonAlphaEstimateScaledAt18 : Nat
  estimateSourceAbsDiffScaledAt18 : Nat
  estimateWithinMachineEpsilon : Bool
deriving Repr

def neutrinoAlphaRichardsonReportFromState
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (initialState : OrbitCarryState)
    (crankCount coarse middle fine : Nat) :
    NeutrinoAlphaRichardsonReport :=
  let coarseStudy :=
    neutrinoAlphaRichardsonStudyPointFromState aperture read initialState
      coarse
  let middleStudy :=
    neutrinoAlphaRichardsonStudyPointFromState aperture read initialState
      middle
  let fineStudy :=
    neutrinoAlphaRichardsonStudyPointFromState aperture read initialState fine
  let firstSlip := neutrinoRichardsonSlip coarseStudy middleStudy
  let secondSlip := neutrinoRichardsonSlip middleStudy fineStudy
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
  let sourceDiff := natAbsDiff midpoint sourceAlpha
  { name := "neutrino-three-crank-alpha-richardson"
    normalization := "h = c = 1"
    crankCount := crankCount
    sourceAlphaScaledAt18 := sourceAlpha
    studies := [coarseStudy, middleStudy, fineStudy]
    firstSlip := firstSlip
    secondSlip := secondSlip
    richardsonBracketLowerScaledAt18 := bracketLower
    richardsonBracketUpperScaledAt18 := bracketUpper
    richardsonBracketWidthScaledAt18 := bracketUpper - bracketLower
    signedSlipsBracketZero :=
      signedValuesBracketZero firstSlip.signedMeanSlipScaledAt18
        secondSlip.signedMeanSlipScaledAt18
    sourceAlphaInsideRichardsonBracket :=
      natWithinBracket bracketLower sourceAlpha bracketUpper
    richardsonAlphaEstimateScaledAt18 := midpoint
    estimateSourceAbsDiffScaledAt18 := sourceDiff
    estimateWithinMachineEpsilon :=
      decide (sourceDiff <= electronMachineEpsilonReport.machineEpsilonScaledAt18) }

def orbitSlipScanStateAfter
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport) :
    Nat -> OrbitSlipScanState -> OrbitSlipScanState
  | 0, state => state
  | fuel + 1, state =>
      orbitSlipScanStateAfter aperture read fuel
        (orbitSlipScanStep aperture read state).nextState

def neutrinoCrankedSlipScan
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (crankCount targetAdditionalOrbits fuel : Nat) :
    OrbitSlipScanReport :=
  let start :=
    orbitSlipScanStateAfter aperture read crankCount
      (initialOrbitSlipScanState aperture.latticePeriod)
  orbitSlipScanAux aperture read
    (start.completedOrbits + targetAdditionalOrbits) fuel start [] []

structure NeutrinoThreeCrankExperimentReport where
  name : String
  antiCooperPairChannelOpen : Bool
  antiCooperPairOccupied : Bool
  antiCooperPairFact : Bool
  electronFact : Bool
  neutrinoResidueFact : Bool
  crankCount : Nat
  crankedState : Option OrbitCarryState
  hundredTrialStudy : Option ElectronAlphaStudyReport
  slipScan : Option OrbitSlipScanReport
  richardson : Option NeutrinoAlphaRichardsonReport
deriving Repr

def defaultNeutrinoThreeCrankExperimentReport? :
    Option NeutrinoThreeCrankExperimentReport :=
  match defaultAdjacentWobbleReport? with
  | none => none
  | some aperture =>
      let read := cavendishChargeMassNormalization
      let cranked := neutrinoCrankStateAfterThree aperture read
      let study := neutrinoAlphaStudyReportFromState aperture read cranked 100
      let slipScan := neutrinoCrankedSlipScan aperture read 3 2 32
      let richardson :=
        neutrinoAlphaRichardsonReportFromState aperture read cranked 3
          10000 20000 40000
      some
        { name := "neutrino-three-crank-experiment"
          antiCooperPairChannelOpen := antiCooperPairChannelOpenBool
          antiCooperPairOccupied := antiCooperPairOccupiedBool
          antiCooperPairFact := factDecision Fact.ANTI_COOPER_PAIR
          electronFact := factDecision Fact.ELECTRON
          neutrinoResidueFact := factDecision Fact.NEUTRINO
          crankCount := 3
          crankedState := some cranked
          hundredTrialStudy := some study
          slipScan := some slipScan
          richardson := some richardson }

#eval defaultNeutrinoThreeCrankExperimentReport?

end Measurement
