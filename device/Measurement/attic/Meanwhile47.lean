import Measurement.Meanwhile46

set_option maxRecDepth 2048

/- MEANWHILE 47 -- GRID TWO ORBITS AND BRACKET BOTH SLIPS. The elaborator now
reports a wrapped angular position. A slip is the grid edge where the carried
residue crosses one full turn and wraps back through zero.

This file keeps the selected-neighborhood PRNG in the loop, walks until two
full-turn crossings have occurred, and records the adjacent grid cell that
brackets each crossing.
-/

namespace Measurement

structure OrbitSlipScanState where
  steps : Nat
  seed : Nat
  selectedFace : CorridorFace
  latticeDenominator : Nat
  completedOrbits : Nat
  carriedResidueNumerator : Nat
deriving Repr

structure OrbitSlipGridCell where
  lowerStep : Nat
  upperStep : Nat
  seedIn : Nat
  seedOut : Nat
  selectedFace : CorridorFace
  orbitBefore : Nat
  orbitAfter : Nat
  residueBefore : Nat
  projectedResidue : Nat
  residueRaw : Nat
  residueAfter : Nat
  slipped : Bool
  lowerTurnScaledAt18 : Nat
  upperTurnScaledAt18 : Nat
  lowerRadiansScaledAt18 : Nat
  upperRadiansScaledAt18 : Nat
  carriedRadiansAfterScaledAt18 : Nat
deriving Repr

structure OrbitSlipBracket where
  slipIndex : Nat
  lowerStep : Nat
  upperStep : Nat
  selectedFace : CorridorFace
  latticeDenominator : Nat
  lowerResidueNumerator : Nat
  upperResidueRawNumerator : Nat
  lowerTurnScaledAt18 : Nat
  upperTurnScaledAt18 : Nat
  slipBoundaryTurnScaledAt18 : Nat
  lowerRadiansScaledAt18 : Nat
  upperRadiansScaledAt18 : Nat
  slipBoundaryRadiansScaledAt18 : Nat
  bracketWidthRadiansScaledAt18 : Nat
deriving Repr

structure OrbitSlipStep where
  cell : OrbitSlipGridCell
  bracket? : Option OrbitSlipBracket
  nextState : OrbitSlipScanState
deriving Repr

structure OrbitSlipScanReport where
  targetOrbitCount : Nat
  gridStepLimit : Nat
  completedOrbitCount : Nat
  gridCellCount : Nat
  bracketCount : Nat
  grid : List OrbitSlipGridCell
  brackets : List OrbitSlipBracket
deriving Repr

def initialOrbitSlipScanState (latticeDenominator : Nat) :
    OrbitSlipScanState :=
  { steps := 0
    seed := CooperManual.initialSeed
    selectedFace := .charge
    latticeDenominator := latticeDenominator
    completedOrbits := 0
    carriedResidueNumerator := 0 }

def absoluteTurnFromNumerator
    (latticeDenominator absoluteNumerator : Nat) : ApparatusRatio :=
  { numerator := absoluteNumerator, denominator := latticeDenominator }

def orbitSlipScanStep
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (state : OrbitSlipScanState) : OrbitSlipStep :=
  let report := neighborhoodDeciderReport state.seed aperture read
  let orbitRead := neighborhoodOrbitRead report
  let projectedResidue :=
    projectRatioNumeratorToDenominator state.latticeDenominator
      orbitRead.meanResidueTurn
  let residueRaw := state.carriedResidueNumerator + projectedResidue
  let orbitDelta := residueRaw / state.latticeDenominator
  let residueAfter := residueRaw % state.latticeDenominator
  let orbitAfter := state.completedOrbits + orbitDelta
  let slipped := !(orbitDelta == 0)
  let lowerAbsoluteNumerator :=
    state.completedOrbits * state.latticeDenominator +
      state.carriedResidueNumerator
  let upperAbsoluteNumerator :=
    state.completedOrbits * state.latticeDenominator + residueRaw
  let lowerTurn :=
    absoluteTurnFromNumerator state.latticeDenominator lowerAbsoluteNumerator
  let upperTurn :=
    absoluteTurnFromNumerator state.latticeDenominator upperAbsoluteNumerator
  let lowerRadians := lowerTurn.turnsAsRadians
  let upperRadians := upperTurn.turnsAsRadians
  let carriedAfterTurn : ApparatusRatio :=
    { numerator := residueAfter, denominator := state.latticeDenominator }
  let carriedAfterRadians := carriedAfterTurn.turnsAsRadians
  let cell :=
    { lowerStep := state.steps
      upperStep := state.steps + 1
      seedIn := state.seed
      seedOut := report.seedOut
      selectedFace := report.selectedFace
      orbitBefore := state.completedOrbits
      orbitAfter := orbitAfter
      residueBefore := state.carriedResidueNumerator
      projectedResidue := projectedResidue
      residueRaw := residueRaw
      residueAfter := residueAfter
      slipped := slipped
      lowerTurnScaledAt18 := lowerTurn.scaledFloor (pow10 18)
      upperTurnScaledAt18 := upperTurn.scaledFloor (pow10 18)
      lowerRadiansScaledAt18 := lowerRadians.scaledFloor (pow10 18)
      upperRadiansScaledAt18 := upperRadians.scaledFloor (pow10 18)
      carriedRadiansAfterScaledAt18 :=
        carriedAfterRadians.scaledFloor (pow10 18) }
  let bracket? :=
    if slipped then
      let slipIndex := state.completedOrbits + 1
      let boundaryRadians := twoPiRatio.mulNat slipIndex
      some
        { slipIndex := slipIndex
          lowerStep := state.steps
          upperStep := state.steps + 1
          selectedFace := report.selectedFace
          latticeDenominator := state.latticeDenominator
          lowerResidueNumerator := state.carriedResidueNumerator
          upperResidueRawNumerator := residueRaw
          lowerTurnScaledAt18 := lowerTurn.scaledFloor (pow10 18)
          upperTurnScaledAt18 := upperTurn.scaledFloor (pow10 18)
          slipBoundaryTurnScaledAt18 := slipIndex * pow10 18
          lowerRadiansScaledAt18 := lowerRadians.scaledFloor (pow10 18)
          upperRadiansScaledAt18 := upperRadians.scaledFloor (pow10 18)
          slipBoundaryRadiansScaledAt18 :=
            boundaryRadians.scaledFloor (pow10 18)
          bracketWidthRadiansScaledAt18 :=
            (positiveRatioDifference upperRadians lowerRadians).scaledAt18 }
    else
      none
  { cell := cell
    bracket? := bracket?
    nextState :=
      { steps := state.steps + 1
        seed := report.seedOut
        selectedFace := report.selectedFace
        latticeDenominator := state.latticeDenominator
        completedOrbits := orbitAfter
        carriedResidueNumerator := residueAfter } }

def appendBracket
    (brackets : List OrbitSlipBracket) :
    Option OrbitSlipBracket -> List OrbitSlipBracket
  | none => brackets
  | some bracket => brackets ++ [bracket]

def orbitSlipScanAux
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (targetOrbitCount : Nat) :
    Nat -> OrbitSlipScanState -> List OrbitSlipGridCell ->
      List OrbitSlipBracket -> OrbitSlipScanReport
  | 0, state, grid, brackets =>
      { targetOrbitCount := targetOrbitCount
        gridStepLimit := state.steps
        completedOrbitCount := state.completedOrbits
        gridCellCount := grid.length
        bracketCount := brackets.length
        grid := grid
        brackets := brackets }
  | fuel + 1, state, grid, brackets =>
      if targetOrbitCount ≤ state.completedOrbits then
        { targetOrbitCount := targetOrbitCount
          gridStepLimit := state.steps
          completedOrbitCount := state.completedOrbits
          gridCellCount := grid.length
          bracketCount := brackets.length
          grid := grid
          brackets := brackets }
      else
        let step := orbitSlipScanStep aperture read state
        orbitSlipScanAux aperture read targetOrbitCount fuel step.nextState
          (grid ++ [step.cell]) (appendBracket brackets step.bracket?)

def orbitSlipScan
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (targetOrbitCount fuel : Nat) : OrbitSlipScanReport :=
  orbitSlipScanAux aperture read targetOrbitCount fuel
    (initialOrbitSlipScanState aperture.latticePeriod) [] []

def defaultTwoOrbitSlipScan? : Option OrbitSlipScanReport :=
  defaultAdjacentWobbleReport?.map fun aperture =>
    orbitSlipScan aperture cavendishChargeMassNormalization 2 32

def orbitSlipProbe : Nat :=
  match defaultTwoOrbitSlipScan? with
  | none => 0
  | some report =>
      report.completedOrbitCount * pow10 18 +
        report.gridCellCount * report.bracketCount

register_heart_rate_as twoOrbitSlipGridHeartbeat orbitSlipProbe

structure TwoOrbitSlipGridReceipt where
  heartbeat : Nat
  scan : Option OrbitSlipScanReport
deriving Repr

def twoOrbitSlipGridReceipt : TwoOrbitSlipGridReceipt :=
  { heartbeat := twoOrbitSlipGridHeartbeat
    scan := defaultTwoOrbitSlipScan? }

#eval twoOrbitSlipGridReceipt

end Measurement
