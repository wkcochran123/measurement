import Measurement.Meanwhile49

set_option maxRecDepth 4096

/- MEANWHILE 50 -- THE ALPHA STUDY. The electron fact gives the apparatus a
current state. A study should not re-create the charge measurement from scratch
one hundred times; it should keep the machine alive, advance the carried orbit
state, and read the induced charge wobble at each step.

Each trial reads

  alpha_i = e_i^2 / (4*pi)

with `c = 1`. The carried state advances the decider. The selected face then
chooses one rational electron-charge-square value from the adjacent wobble
aperture: charge = lower square, mass = target square, value = upper square.
The formal `Study` chain records the hundred trials under `Fact.ELECTRON`; the
numeric report records the mean and variance of the scaled alpha readings.
-/

namespace Measurement

def ratioInverseScaledFloor? (q : ApparatusRatio) (scale : Nat) :
    Option Nat :=
  if q.numerator = 0 then
    none
  else
    some (q.inverseScaledFloor scale)

def meanNatFloor (values : List Nat) : Nat :=
  match values.length with
  | 0 => 0
  | count => values.foldl (fun sum value => sum + value) 0 / count

def varianceNatScaledAt36 (values : List Nat) : Nat :=
  match values.length with
  | 0 => 0
  | count =>
      let mean := meanNatFloor values
      values.foldl
        (fun sum value => sum + square (natAbsDiff value mean)) 0 / count

def varianceNatScaledAt18 (values : List Nat) : Nat :=
  varianceNatScaledAt36 values / pow10 18

structure ElectronAlphaExperimentRead where
  index : Nat
  seedIn : Nat
  seedOut : Nat
  selectedFace : CorridorFace
  residueNumeratorBefore : Nat
  residueNumeratorAfter : Nat
  carriedResidueTurnScaledAt18 : Nat
  sampledChargeSquaredScaledAt18 : Nat
  alphaScaledAt18 : Nat
  inverseAlphaScaledAt18? : Option Nat
deriving Repr

def electronAlphaChargeSquaredForFace
    (aperture : AdjacentWobbleReport) :
    CorridorFace -> ApparatusRatio
  | .charge => aperture.lowerSquare
  | .mass => aperture.targetElementaryChargeSquared
  | .value => aperture.upperSquare

def electronAlphaExperimentRead
    (aperture : AdjacentWobbleReport)
    (index : Nat) (state nextState : OrbitCarryState) :
    ElectronAlphaExperimentRead :=
  let sampledChargeSquared :=
    electronAlphaChargeSquaredForFace aperture nextState.selectedFace
  let alpha := electronAlphaFromChargeSquared sampledChargeSquared
  { index := index
    seedIn := state.seed
    seedOut := nextState.seed
    selectedFace := nextState.selectedFace
    residueNumeratorBefore := state.carriedResidueNumerator
    residueNumeratorAfter := nextState.carriedResidueNumerator
    carriedResidueTurnScaledAt18 :=
      nextState.carriedResidueTurnScaledAt18
    sampledChargeSquaredScaledAt18 :=
      sampledChargeSquared.scaledFloor (pow10 18)
    alphaScaledAt18 := alpha.scaledFloor (pow10 18)
    inverseAlphaScaledAt18? := ratioInverseScaledFloor? alpha (pow10 18) }

structure ElectronAlphaStudyAccumulator where
  index : Nat
  state : OrbitCarryState
  samples : List ElectronAlphaExperimentRead

def electronAlphaStudyInitialState
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport) : OrbitCarryState :=
  orbitCarryRun aperture read electronCompletedTurns
    (initialOrbitCarryState aperture.latticePeriod)

def electronAlphaStudyFold
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (acc : ElectronAlphaStudyAccumulator) (_ : Nat) :
    ElectronAlphaStudyAccumulator :=
  let nextState := orbitCarryStep aperture read acc.state
  let sample := electronAlphaExperimentRead aperture acc.index acc.state nextState
  { index := acc.index + 1
    state := nextState
    samples := acc.samples ++ [sample] }

def electronAlphaStudyRun
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (trialCount : Nat) : ElectronAlphaStudyAccumulator :=
  (List.range trialCount).foldl (electronAlphaStudyFold aperture read)
    { index := 0
      state := electronAlphaStudyInitialState aperture read
      samples := [] }

def electronAlphaStudyLimit : Limit :=
  .nil Fact.ELECTRON

def electronAlphaStudySample : Sample :=
  .initial_condition Fact.ELECTRON electronAlphaStudyLimit

def electronAlphaStudyTrial : Trial :=
  .hypothesis Fact.ELECTRON electronAlphaStudySample

def electronAlphaFormalStudyAux : Nat -> Study -> Study
  | 0, study => study
  | fuel + 1, study =>
      electronAlphaFormalStudyAux fuel
        (.data Fact.ELECTRON electronAlphaStudyTrial study)

def electronAlphaFormalStudy (trialCount : Nat) : Study :=
  electronAlphaFormalStudyAux trialCount (.hypothesis Fact.ELECTRON)

def studyDataCount : Study -> Nat
  | .hypothesis _ => 0
  | .data _ _ rest => studyDataCount rest + 1

def electronAlphaStudyFaceCount
    (samples : List ElectronAlphaExperimentRead)
    (face : CorridorFace) : Nat :=
  samples.foldl
    (fun count sample =>
      if sample.selectedFace = face then count + 1 else count) 0

structure ElectronAlphaStudyReport where
  name : String
  normalization : String
  cSetToOne : Bool
  startsFromElectronState : Bool
  startingCompletedTurns : Nat
  trialCount : Nat
  formalStudyDepth : Nat
  initialSeed : Nat
  finalSeed : Nat
  initialResidueNumerator : Nat
  finalResidueNumerator : Nat
  chargeFaceSamples : Nat
  massFaceSamples : Nat
  valueFaceSamples : Nat
  sourceAlphaScaledAt18 : Nat
  meanSourceAbsDiffScaledAt18 : Nat
  sampleAlphaMeanScaledAt18 : Nat
  sampleMeanInverseAlphaScaledAt18? : Option Nat
  sampleAlphaVarianceScaledAt18 : Nat
  sampleAlphaVarianceScaledAt36 : Nat
  firstFiveSamples : List ElectronAlphaExperimentRead
  lastFiveSamples : List ElectronAlphaExperimentRead
deriving Repr

def electronAlphaStudyReport
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (trialCount : Nat) : ElectronAlphaStudyReport :=
  let initialState := electronAlphaStudyInitialState aperture read
  let run := electronAlphaStudyRun aperture read trialCount
  let alphaSamples := run.samples.map fun sample => sample.alphaScaledAt18
  let sourceAlpha :=
    electronAlphaFromChargeSquared aperture.targetElementaryChargeSquared
  let sourceAlphaScaledAt18 := sourceAlpha.scaledFloor (pow10 18)
  let sampleMean := meanNatFloor alphaSamples
  { name := "electron-alpha-carried-wobble-study"
    normalization := "h = c = 1"
    cSetToOne := true
    startsFromElectronState := true
    startingCompletedTurns := electronCompletedTurns
    trialCount := trialCount
    formalStudyDepth := studyDataCount (electronAlphaFormalStudy trialCount)
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

def defaultElectronAlphaStudyReport? : Option ElectronAlphaStudyReport :=
  defaultAdjacentWobbleReport?.map fun aperture =>
    electronAlphaStudyReport aperture cavendishChargeMassNormalization 100

#eval defaultElectronAlphaStudyReport?

def electronAlphaAtIndexScaledAt18
    (aperture : AdjacentWobbleReport) (index : Nat) : Nat :=
  let face := electronCorridorFace (electronFromIndex index)
  let chargeSquared := electronAlphaChargeSquaredForFace aperture face
  (electronAlphaFromChargeSquared chargeSquared).scaledFloor (pow10 18)

def signedScaledDelta (fromValue toValue : Nat) : Int :=
  Int.ofNat toValue - Int.ofNat fromValue

structure ElectronAlphaPathRelationReport where
  left : Nat
  middle : Nat
  right : Nat
  leftFace : CorridorFace
  middleFace : CorridorFace
  rightFace : CorridorFace
  oneToTwoResidueNat : Nat
  twoToThreeResidueNat : Nat
  composedResidueNat : Nat
  directResidueNat : Nat
  corridorResiduesRelated : Bool
  leftAlphaScaledAt18 : Nat
  middleAlphaScaledAt18 : Nat
  rightAlphaScaledAt18 : Nat
  signedOneToTwoAlphaDeltaScaledAt18 : Int
  signedTwoToThreeAlphaDeltaScaledAt18 : Int
  signedComposedAlphaDeltaScaledAt18 : Int
  signedDirectAlphaDeltaScaledAt18 : Int
  signedDeltasRelated : Bool
  absoluteOneToTwoAlphaDeltaScaledAt18 : Nat
  absoluteTwoToThreeAlphaDeltaScaledAt18 : Nat
  absoluteComposedPathLengthScaledAt18 : Nat
  absoluteDirectPathLengthScaledAt18 : Nat
  absolutePathLengthsRelated : Bool
  absoluteTriangleExcessScaledAt18 : Nat
deriving Repr

def electronAlphaPathRelationReport
    (aperture : AdjacentWobbleReport)
    (left middle right : Nat) : ElectronAlphaPathRelationReport :=
  let leftFace := electronCorridorFace (electronFromIndex left)
  let middleFace := electronCorridorFace (electronFromIndex middle)
  let rightFace := electronCorridorFace (electronFromIndex right)
  let oneToTwoResidue := electronForwardResidueNat left middle
  let twoToThreeResidue := electronForwardResidueNat middle right
  let composedResidue := oneToTwoResidue + twoToThreeResidue
  let directResidue := electronForwardResidueNat left right
  let leftAlpha := electronAlphaAtIndexScaledAt18 aperture left
  let middleAlpha := electronAlphaAtIndexScaledAt18 aperture middle
  let rightAlpha := electronAlphaAtIndexScaledAt18 aperture right
  let signedOneToTwo := signedScaledDelta leftAlpha middleAlpha
  let signedTwoToThree := signedScaledDelta middleAlpha rightAlpha
  let signedComposed := signedOneToTwo + signedTwoToThree
  let signedDirect := signedScaledDelta leftAlpha rightAlpha
  let absoluteOneToTwo := natAbsDiff leftAlpha middleAlpha
  let absoluteTwoToThree := natAbsDiff middleAlpha rightAlpha
  let absoluteComposed := absoluteOneToTwo + absoluteTwoToThree
  let absoluteDirect := natAbsDiff leftAlpha rightAlpha
  { left := left
    middle := middle
    right := right
    leftFace := leftFace
    middleFace := middleFace
    rightFace := rightFace
    oneToTwoResidueNat := oneToTwoResidue
    twoToThreeResidueNat := twoToThreeResidue
    composedResidueNat := composedResidue
    directResidueNat := directResidue
    corridorResiduesRelated :=
      decide (composedResidue = directResidue)
    leftAlphaScaledAt18 := leftAlpha
    middleAlphaScaledAt18 := middleAlpha
    rightAlphaScaledAt18 := rightAlpha
    signedOneToTwoAlphaDeltaScaledAt18 := signedOneToTwo
    signedTwoToThreeAlphaDeltaScaledAt18 := signedTwoToThree
    signedComposedAlphaDeltaScaledAt18 := signedComposed
    signedDirectAlphaDeltaScaledAt18 := signedDirect
    signedDeltasRelated :=
      decide (signedComposed = signedDirect)
    absoluteOneToTwoAlphaDeltaScaledAt18 := absoluteOneToTwo
    absoluteTwoToThreeAlphaDeltaScaledAt18 := absoluteTwoToThree
    absoluteComposedPathLengthScaledAt18 := absoluteComposed
    absoluteDirectPathLengthScaledAt18 := absoluteDirect
    absolutePathLengthsRelated :=
      decide (absoluteComposed = absoluteDirect)
    absoluteTriangleExcessScaledAt18 :=
      natAbsDiff absoluteComposed absoluteDirect }

def defaultElectronAlphaPathRelationReport? :
    Option ElectronAlphaPathRelationReport :=
  defaultAdjacentWobbleReport?.map fun aperture =>
    electronAlphaPathRelationReport aperture 1 2 3

#eval defaultElectronAlphaPathRelationReport?

structure ElectronAlphaRichardsonStudyPoint where
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

structure ElectronAlphaRichardsonAccumulator where
  index : Nat
  state : OrbitCarryState
  chargeFaceSamples : Nat
  massFaceSamples : Nat
  valueFaceSamples : Nat
  alphaSumScaledAt18 : Nat
  alphaSquareSumScaledAt36 : Nat

def varianceFromSumScaledAt36
    (count sum sumSq mean : Nat) : Nat :=
  match count with
  | 0 => 0
  | n =>
      (sumSq + n * mean * mean - 2 * mean * sum) / n

def electronAlphaRichardsonStudyFold
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (acc : ElectronAlphaRichardsonAccumulator) (_ : Nat) :
    ElectronAlphaRichardsonAccumulator :=
  let nextState := orbitCarryStep aperture read acc.state
  let sampledChargeSquared :=
    electronAlphaChargeSquaredForFace aperture nextState.selectedFace
  let alphaScaled :=
    (electronAlphaFromChargeSquared sampledChargeSquared).scaledFloor
      (pow10 18)
  let chargeFaceSamples :=
    if nextState.selectedFace = .charge then acc.chargeFaceSamples + 1
    else acc.chargeFaceSamples
  let massFaceSamples :=
    if nextState.selectedFace = .mass then acc.massFaceSamples + 1
    else acc.massFaceSamples
  let valueFaceSamples :=
    if nextState.selectedFace = .value then acc.valueFaceSamples + 1
    else acc.valueFaceSamples
  { index := acc.index + 1
    state := nextState
    chargeFaceSamples := chargeFaceSamples
    massFaceSamples := massFaceSamples
    valueFaceSamples := valueFaceSamples
    alphaSumScaledAt18 := acc.alphaSumScaledAt18 + alphaScaled
    alphaSquareSumScaledAt36 :=
      acc.alphaSquareSumScaledAt36 + alphaScaled * alphaScaled }

def electronAlphaRichardsonStudyPoint
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (trialCount : Nat) : ElectronAlphaRichardsonStudyPoint :=
  let initialState := electronAlphaStudyInitialState aperture read
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

def richardsonOrderOneScaledAt18 (coarse fine : Nat) : Nat :=
  2 * fine - coarse

def natBracketLower (a b : Nat) : Nat :=
  if a <= b then a else b

def natBracketUpper (a b : Nat) : Nat :=
  if a <= b then b else a

def natWithinBracket (lower value upper : Nat) : Bool :=
  decide (lower <= value) && decide (value <= upper)

def signedValuesBracketZero (a b : Int) : Bool :=
  (decide (a <= 0) && decide (0 <= b)) ||
    (decide (b <= 0) && decide (0 <= a))

structure ElectronAlphaRichardsonSlip where
  lowerTrialCount : Nat
  upperTrialCount : Nat
  lowerMeanAlphaScaledAt18 : Nat
  upperMeanAlphaScaledAt18 : Nat
  signedMeanSlipScaledAt18 : Int
  absoluteMeanSlipScaledAt18 : Nat
  richardsonAlphaScaledAt18 : Nat
deriving Repr

def electronAlphaRichardsonSlip
    (lower upper : ElectronAlphaRichardsonStudyPoint) :
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

structure ElectronAlphaRichardsonReport where
  name : String
  normalization : String
  refinementRatio : Nat
  richardsonOrder : Nat
  sourceAlphaScaledAt18 : Nat
  studies : List ElectronAlphaRichardsonStudyPoint
  firstSlip : ElectronAlphaRichardsonSlip
  secondSlip : ElectronAlphaRichardsonSlip
  orbitSlipBrackets : List OrbitCorridorSlipRead
  richardsonBracketLowerScaledAt18 : Nat
  richardsonBracketUpperScaledAt18 : Nat
  richardsonBracketWidthScaledAt18 : Nat
  signedSlipsBracketZero : Bool
  fineStudyMeanInsideRichardsonBracket : Bool
  richardsonAlphaEstimateScaledAt18 : Nat
  estimateSourceAbsDiffScaledAt18 : Nat
deriving Repr

def electronAlphaRichardsonReport
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (corridor : OrbitCorridorReport)
    (coarse middle fine : Nat) : ElectronAlphaRichardsonReport :=
  let coarseStudy := electronAlphaRichardsonStudyPoint aperture read coarse
  let middleStudy := electronAlphaRichardsonStudyPoint aperture read middle
  let fineStudy := electronAlphaRichardsonStudyPoint aperture read fine
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
  { name := "electron-alpha-richardson-slip-bracket"
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

def defaultElectronAlphaRichardsonReport? :
    Option ElectronAlphaRichardsonReport :=
  match defaultAdjacentWobbleReport?, defaultOrbitCorridorReport? with
  | some aperture, some corridor =>
      some
        (electronAlphaRichardsonReport aperture
          cavendishChargeMassNormalization corridor 10000 20000 40000)
  | _, _ => none

#eval defaultElectronAlphaRichardsonReport?

end Measurement
