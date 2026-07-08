import Measurement.Meanwhile48

set_option maxRecDepth 2048

/- MEANWHILE 49 -- THE ELECTRON FACT GROUNDS THE FIRST THREE RUNGS. The orbit
decider now counts completed turns, and the corridor interprets those turns.
This closes the base interface by making the electron a concrete fact and using
that fact to implement distinguishable, admissible, and countable.
-/

namespace Measurement

structure Electron where
  number : Number

def electronCorridorTruthBool : Bool :=
  match defaultOrbitCorridorReport? with
  | some report =>
      decide (report.initialCorridorFace = .charge) &&
        decide (report.countedTurns = 2) &&
        decide (report.activeCorridorFace = .value)
  | none => false

def electronCorridorTruth : Prop :=
  electronCorridorTruthBool = true

namespace Fact

def ELECTRON : Fact :=
  { truth := electronCorridorTruth
    decTruth :=
      show Decidable (electronCorridorTruthBool = true) from
        if h : electronCorridorTruthBool = true then
          isTrue h
        else
          isFalse h }

end Fact

def electronCompletedTurns : Nat :=
  match defaultOrbitCorridorReport? with
  | some report => report.countedTurns
  | none => 0

def electronReducedTurns : Nat :=
  corridorReducedTurns electronCompletedTurns

def electronActiveCorridorFace : CorridorFace :=
  CorridorFace.ofTurns electronCompletedTurns

def electronNumberFromNat : Nat -> Number
  | 0 => .zero Fact.ELECTRON
  | n + 1 => .one Fact.ELECTRON (electronNumberFromNat n)

def electronFromNumber (number : Number) : Electron :=
  { number := number }

def electron0 : Electron :=
  electronFromNumber (electronNumberFromNat 0)

def electron1 : Electron :=
  electronFromNumber (electronNumberFromNat 1)

def electron2 : Electron :=
  electronFromNumber (electronNumberFromNat 2)

def electron3 : Electron :=
  electronFromNumber (electronNumberFromNat 3)

def threeElectrons : List Electron :=
  [electron0, electron1, electron2]

def electronQuartet : List Electron :=
  [electron0, electron1, electron2, electron3]

def electronNumberRead (electron : Electron) : Nat :=
  electron.number.corridorDepth

def electronCorridorFace (electron : Electron) : CorridorFace :=
  CorridorFace.ofTurns electron.number.corridorDepth

def electronSameByCorridor (left right : Electron) : Prop :=
  electronCorridorFace left = electronCorridorFace right

def CorridorFace.sameBool : CorridorFace -> CorridorFace -> Bool
  | .charge, .charge => true
  | .mass, .mass => true
  | .value, .value => true
  | _, _ => false

def electronSameByCorridorBool (left right : Electron) : Bool :=
  CorridorFace.sameBool (electronCorridorFace left) (electronCorridorFace right)

def electronFromIndex (index : Nat) : Electron :=
  electronFromNumber (electronNumberFromNat index)

def electronSameByIndexBool (left right : Nat) : Bool :=
  electronSameByCorridorBool (electronFromIndex left) (electronFromIndex right)

structure ElectronSamenessRead where
  left : Nat
  right : Nat
  leftFace : CorridorFace
  rightFace : CorridorFace
  same : Bool
deriving Repr

def electronSamenessRead (left right : Nat) : ElectronSamenessRead :=
  let leftElectron := electronFromIndex left
  let rightElectron := electronFromIndex right
  { left := left
    right := right
    leftFace := electronCorridorFace leftElectron
    rightFace := electronCorridorFace rightElectron
    same := electronSameByCorridorBool leftElectron rightElectron }

def electronQuartetSamenessReads : List ElectronSamenessRead :=
  [ electronSamenessRead 0 0, electronSamenessRead 0 1,
    electronSamenessRead 0 2, electronSamenessRead 0 3,
    electronSamenessRead 1 0, electronSamenessRead 1 1,
    electronSamenessRead 1 2, electronSamenessRead 1 3,
    electronSamenessRead 2 0, electronSamenessRead 2 1,
    electronSamenessRead 2 2, electronSamenessRead 2 3,
    electronSamenessRead 3 0, electronSamenessRead 3 1,
    electronSamenessRead 3 2, electronSamenessRead 3 3 ]

def electronQuartetHasSame : Bool :=
  electronSameByIndexBool 0 1 || electronSameByIndexBool 0 2 ||
    electronSameByIndexBool 0 3 || electronSameByIndexBool 1 2 ||
    electronSameByIndexBool 1 3 || electronSameByIndexBool 2 3

theorem threeElectrons_count : threeElectrons.length = 3 := rfl

theorem threeElectrons_number_reads :
    threeElectrons.map electronNumberRead = [0, 1, 2] := rfl

theorem electronQuartet_count : electronQuartet.length = 4 := rfl

theorem electronQuartet_number_reads :
    electronQuartet.map electronNumberRead = [0, 1, 2, 3] := rfl

theorem electronQuartet_faces :
    electronQuartet.map electronCorridorFace =
      [CorridorFace.charge, CorridorFace.mass, CorridorFace.value,
        CorridorFace.charge] := rfl

theorem electron_quartet_zero_three_same :
    electronSameByCorridor electron0 electron3 := rfl

theorem electron_quartet_has_same :
    electronQuartetHasSame = true := by
  decide

theorem electron_zero_three_quotient_same :
    Quot.mk electronSameByCorridor electron0 =
      Quot.mk electronSameByCorridor electron3 :=
  selection_sound electron_quartet_zero_three_same

def electronForwardResidueNat (left right : Nat) : Nat :=
  (electronNumberRead (electronFromIndex right) + corridorPeriod -
      electronNumberRead (electronFromIndex left)) % corridorPeriod

def electronForwardResidueNumber (left right : Nat) : Number :=
  electronNumberFromNat (electronForwardResidueNat left right)

structure ElectronResidueRead where
  left : Nat
  right : Nat
  leftFace : CorridorFace
  rightFace : CorridorFace
  residueNat : Nat
  residueNumberDepth : Nat
deriving Repr

def electronResidueRead (left right : Nat) : ElectronResidueRead :=
  let leftElectron := electronFromIndex left
  let rightElectron := electronFromIndex right
  let residueNumber := electronForwardResidueNumber left right
  { left := left
    right := right
    leftFace := electronCorridorFace leftElectron
    rightFace := electronCorridorFace rightElectron
    residueNat := electronForwardResidueNat left right
    residueNumberDepth := residueNumber.corridorDepth }

def electronAdjacentResidueNat : Nat :=
  electronForwardResidueNat 1 2 + electronForwardResidueNat 2 3

def electronAdjacentResidueNumber : Number :=
  electronNumberFromNat electronAdjacentResidueNat

def electronDirectResidueNat : Nat :=
  electronForwardResidueNat 1 3

def electronDirectResidueNumber : Number :=
  electronForwardResidueNumber 1 3

inductive ElectronResidueComparison where
  | adjacentBigger
  | directBigger
  | equal
deriving Repr, DecidableEq

def compareResidueDepths (adjacent direct : Nat) :
    ElectronResidueComparison :=
  if direct < adjacent then
    .adjacentBigger
  else if adjacent < direct then
    .directBigger
  else
    .equal

def electronResidueComparison : ElectronResidueComparison :=
  compareResidueDepths electronAdjacentResidueNumber.corridorDepth
    electronDirectResidueNumber.corridorDepth

structure ElectronResidueComparisonReport where
  oneToTwo : ElectronResidueRead
  twoToThree : ElectronResidueRead
  adjacentResidueNat : Nat
  adjacentResidueNumberDepth : Nat
  oneToThree : ElectronResidueRead
  directResidueNat : Nat
  directResidueNumberDepth : Nat
  comparison : ElectronResidueComparison
deriving Repr

def electronResidueComparisonReport : ElectronResidueComparisonReport :=
  { oneToTwo := electronResidueRead 1 2
    twoToThree := electronResidueRead 2 3
    adjacentResidueNat := electronAdjacentResidueNat
    adjacentResidueNumberDepth := electronAdjacentResidueNumber.corridorDepth
    oneToThree := electronResidueRead 1 3
    directResidueNat := electronDirectResidueNat
    directResidueNumberDepth := electronDirectResidueNumber.corridorDepth
    comparison := electronResidueComparison }

def electronCompilerTraceComparisonReport : ElectronResidueComparisonReport :=
  electronResidueComparisonReport

theorem electron_adjacent_residue_number_eq_direct :
    electronAdjacentResidueNumber = electronDirectResidueNumber := rfl

theorem electron_residue_comparison_equal :
    electronResidueComparison = .equal := by
  decide

def electronComposedTraceNumberDepth : Nat :=
  (electronForwardResidueNumber 1 2).corridorDepth +
    (electronForwardResidueNumber 2 3).corridorDepth

def electronDirectTraceNumberDepth : Nat :=
  (electronForwardResidueNumber 1 3).corridorDepth

theorem electron_composed_trace_depth_eq_direct :
    electronComposedTraceNumberDepth = electronDirectTraceNumberDepth := rfl

register_heart_rate_as electronTraceComposed_warmup
  (electronComposedTraceNumberDepth)
register_heart_rate_as electronTraceComposed_r2
  (electronComposedTraceNumberDepth)
register_heart_rate_as electronTraceComposed_r3
  (electronComposedTraceNumberDepth)
register_heart_rate_as electronTraceComposed_r4
  (electronComposedTraceNumberDepth)
register_heart_rate_as electronTraceDirect_warmup
  (electronDirectTraceNumberDepth)
register_heart_rate_as electronTraceDirect_r2
  (electronDirectTraceNumberDepth)
register_heart_rate_as electronTraceDirect_r3
  (electronDirectTraceNumberDepth)
register_heart_rate_as electronTraceDirect_r4
  (electronDirectTraceNumberDepth)

def electronCostAbsDiff (left right : Nat) : Nat :=
  if left < right then
    right - left
  else
    left - right

def electronHeartbeatStable (left right : Nat) : Bool :=
  decide (left = right ∨ left + 1 = right ∨ right + 1 = left)

def electronHeartbeatWithin (tolerance left right : Nat) : Bool :=
  decide (electronCostAbsDiff left right <= tolerance)

def electronTraceElaborationCostDelta : Nat :=
  electronCostAbsDiff electronTraceComposed_r3 electronTraceDirect_r3

def electronTraceComposedSettlingWidth : Nat :=
  electronCostAbsDiff electronTraceComposed_r3 electronTraceComposed_r4

def electronTraceDirectSettlingWidth : Nat :=
  electronCostAbsDiff electronTraceDirect_r3 electronTraceDirect_r4

def electronMachineEpsilonHeartbeat : Nat :=
  Nat.max 1
    (Nat.max electronTraceComposedSettlingWidth
      electronTraceDirectSettlingWidth)

def electronTraceElaborationCostScale : Nat :=
  Nat.max 1 (Nat.max electronTraceComposed_r3 electronTraceDirect_r3)

def electronElaborationDeltaResolvesAboveEpsilon : Bool :=
  decide (electronMachineEpsilonHeartbeat < electronTraceElaborationCostDelta)

def electronMachineEpsilonRatio : ApparatusRatio :=
  { numerator := electronMachineEpsilonHeartbeat
    denominator := electronTraceElaborationCostScale }

inductive ElectronElaborationCostComparison where
  | composedBigger
  | directBigger
  | equal
deriving Repr, DecidableEq

def electronElaborationCostComparison :
    ElectronElaborationCostComparison :=
  if electronTraceDirect_r3 < electronTraceComposed_r3 then
    .composedBigger
  else if electronTraceComposed_r3 < electronTraceDirect_r3 then
    .directBigger
  else
    .equal

structure ElectronMachineEpsilonReport where
  composedTraceNumberDepth : Nat
  directTraceNumberDepth : Nat
  traceNumbersEqual : Bool
  composedWarmupHeartbeats : Nat
  composedElaborationCost : Nat
  composedStabilityRead : Nat
  composedSettlingWidth : Nat
  composedWithinOneHeartbeat : Bool
  composedWithinMachineEpsilon : Bool
  directWarmupHeartbeats : Nat
  directElaborationCost : Nat
  directStabilityRead : Nat
  directSettlingWidth : Nat
  directWithinOneHeartbeat : Bool
  directWithinMachineEpsilon : Bool
  elaborationCostDelta : Nat
  costComparison : ElectronElaborationCostComparison
  deltaResolvesAboveMachineEpsilon : Bool
  machineEpsilonHeartbeat : Nat
  machineEpsilonScale : Nat
  machineEpsilonScaledAt18 : Nat
deriving Repr

def electronMachineEpsilonReport : ElectronMachineEpsilonReport :=
  { composedTraceNumberDepth := electronComposedTraceNumberDepth
    directTraceNumberDepth := electronDirectTraceNumberDepth
    traceNumbersEqual :=
      decide (electronComposedTraceNumberDepth =
        electronDirectTraceNumberDepth)
    composedWarmupHeartbeats := electronTraceComposed_warmup
    composedElaborationCost := electronTraceComposed_r3
    composedStabilityRead := electronTraceComposed_r4
    composedSettlingWidth := electronTraceComposedSettlingWidth
    composedWithinOneHeartbeat :=
      electronHeartbeatStable electronTraceComposed_r3
        electronTraceComposed_r4
    composedWithinMachineEpsilon :=
      electronHeartbeatWithin electronMachineEpsilonHeartbeat
        electronTraceComposed_r3 electronTraceComposed_r4
    directWarmupHeartbeats := electronTraceDirect_warmup
    directElaborationCost := electronTraceDirect_r3
    directStabilityRead := electronTraceDirect_r4
    directSettlingWidth := electronTraceDirectSettlingWidth
    directWithinOneHeartbeat :=
      electronHeartbeatStable electronTraceDirect_r3
        electronTraceDirect_r4
    directWithinMachineEpsilon :=
      electronHeartbeatWithin electronMachineEpsilonHeartbeat
        electronTraceDirect_r3 electronTraceDirect_r4
    elaborationCostDelta := electronTraceElaborationCostDelta
    costComparison := electronElaborationCostComparison
    deltaResolvesAboveMachineEpsilon :=
      electronElaborationDeltaResolvesAboveEpsilon
    machineEpsilonHeartbeat := electronMachineEpsilonHeartbeat
    machineEpsilonScale := electronTraceElaborationCostScale
    machineEpsilonScaledAt18 :=
      electronMachineEpsilonRatio.scaledFloor (pow10 18) }

def electronAlphaFromChargeSquared
    (chargeSquared : ApparatusRatio) : ApparatusRatio :=
  chargeSquared.div fourPiRatio

structure ElectronAlphaRecoveryReport where
  normalization : String
  cSetToOne : Bool
  denominatorName : String
  denominatorScaledAt18 : Nat
  elementaryChargeSquaredScaledAt18 : Nat
  recoveredAlphaScaledAt18 : Nat
  sourceAlphaScaledAt18 : Nat
  recoveredInverseAlphaScaledAt18 : Nat
  recoveredMatchesSourceAlpha : Bool
  recoveredMatchesFiniteTarget : Bool
deriving Repr

def electronAlphaRecoveryReport
    (report : QuantumChargeLoopReport) : ElectronAlphaRecoveryReport :=
  let recoveredAlpha := electronAlphaFromChargeSquared report.elementaryChargeSquared
  { normalization := report.normalization
    cSetToOne := true
    denominatorName := "4*pi"
    denominatorScaledAt18 := fourPiRatio.scaledFloor (pow10 18)
    elementaryChargeSquaredScaledAt18 :=
      report.elementaryChargeSquaredScaledAt18
    recoveredAlphaScaledAt18 := recoveredAlpha.scaledFloor (pow10 18)
    sourceAlphaScaledAt18 := report.alphaScaledAt18
    recoveredInverseAlphaScaledAt18 :=
      recoveredAlpha.inverseScaledFloor (pow10 18)
    recoveredMatchesSourceAlpha :=
      ratioEquivalent recoveredAlpha report.alpha
    recoveredMatchesFiniteTarget :=
      ratioEquivalent recoveredAlpha fineStructureAlphaTarget }

def defaultElectronAlphaRecoveryReport? :
    Option ElectronAlphaRecoveryReport :=
  defaultQuantumChargeLoopReport?.map electronAlphaRecoveryReport

def electronNaturalFromNat : Nat -> Natural
  | 0 => .zero Fact.ELECTRON
  | n + 1 =>
      .number Fact.ELECTRON (electronNumberFromNat n)
        (electronNaturalFromNat n)

def electronCarrier : CarrierProcess Electron where
  symbol := Fact.ELECTRON
  value := electronNumberFromNat electronCompletedTurns

instance electronDistinguishable :
    DISTINGUISHABLE Electron electronCarrier where
  fact := Fact.ELECTRON
  symbol := Electron
  distinct? := Fact.ELECTRON.truth
  different? := fun _ => Fact.ELECTRON.truth
  dec_distinct := fun _ => Fact.ELECTRON.decTruth

def electronCounting : CountingProcess Electron electronCarrier where
  carrier := electronCarrier
  count := electronNaturalFromNat electronCompletedTurns
  iterate := fun n => .number Fact.ELECTRON electronCarrier.value n

instance electronAdmissible :
    ADMISSIBLE Electron electronCarrier where
  counting_process := electronCounting
  admissible? := fun _ _ => Fact.ELECTRON.truth

def electronIndexing : IndexingProcess Electron electronCarrier where
  count := electronCounting
  origin :=
    .number Fact.ELECTRON electronCounting.count (.zero Fact.ELECTRON)

instance electronCountable :
    COUNTABLE Electron electronCarrier where
  index := electronIndexing
  bounded? := fun _ _ => Fact.ELECTRON.truth

def factDecision (fact : Fact) : Bool :=
  match fact.decTruth with
  | isTrue _ => true
  | isFalse _ => false

def electronDistinctDecision : Bool :=
  match electronDistinguishable.dec_distinct Electron with
  | isTrue _ => true
  | isFalse _ => false

structure ElectronBaseReceipt where
  electronFact : Bool
  completedTurns : Nat
  reducedTurns : Nat
  activeCorridorFace : CorridorFace
  createdElectrons : Nat
  electronNumberReads : List Nat
  quartetElectrons : Nat
  quartetNumberReads : List Nat
  quartetFaces : List CorridorFace
  quartetHasSame : Bool
  quartetSamenessReads : List ElectronSamenessRead
  compilerTraceComparison : ElectronResidueComparisonReport
  machineEpsilon : ElectronMachineEpsilonReport
  alphaRecovery : Option ElectronAlphaRecoveryReport
  distinguishable : Bool
  admissibleAtCount : Bool
  countableAtOrigin : Bool
deriving Repr

def electronBaseReceipt : ElectronBaseReceipt :=
  { electronFact := factDecision Fact.ELECTRON
    completedTurns := electronCompletedTurns
    reducedTurns := electronReducedTurns
    activeCorridorFace := electronActiveCorridorFace
    createdElectrons := threeElectrons.length
    electronNumberReads := threeElectrons.map electronNumberRead
    quartetElectrons := electronQuartet.length
    quartetNumberReads := electronQuartet.map electronNumberRead
    quartetFaces := electronQuartet.map electronCorridorFace
    quartetHasSame := electronQuartetHasSame
    quartetSamenessReads := electronQuartetSamenessReads
    compilerTraceComparison := electronCompilerTraceComparisonReport
    machineEpsilon := electronMachineEpsilonReport
    alphaRecovery := defaultElectronAlphaRecoveryReport?
    distinguishable := electronDistinctDecision
    admissibleAtCount := factDecision Fact.ELECTRON
    countableAtOrigin := factDecision Fact.ELECTRON }

#eval electronBaseReceipt

end Measurement
