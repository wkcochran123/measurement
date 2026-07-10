import Measurement.Meanwhile47

/- MEANWHILE 48 -- PLUG THE TURN DECIDER INTO THE CORRIDOR. The orbit scan
decides when a full turn has actually completed. The corridor should not count
raw grid steps; it should count those completed slips and then interpret the
counted turn through the charge/mass/value corridor.
-/

namespace Measurement

structure OrbitCorridorGridRead where
  lowerStep : Nat
  upperStep : Nat
  selectedNeighborhoodFace : CorridorFace
  slipped : Bool
  turnsBefore : Nat
  turnsAfter : Nat
  corridorFaceBefore : CorridorFace
  corridorFaceAfter : CorridorFace
  reducedTurnsAfter : Nat
  residueAfter : Nat
  carriedRadiansAfterScaledAt18 : Nat
deriving Repr

structure OrbitCorridorSlipRead where
  slipIndex : Nat
  lowerStep : Nat
  upperStep : Nat
  selectedNeighborhoodFace : CorridorFace
  countedTurns : Nat
  reducedTurns : Nat
  corridorFace : CorridorFace
  lowerRadiansScaledAt18 : Nat
  boundaryRadiansScaledAt18 : Nat
  upperRadiansScaledAt18 : Nat
  bracketWidthRadiansScaledAt18 : Nat
deriving Repr

structure OrbitCorridorReport where
  heartbeat : Nat
  targetOrbitCount : Nat
  gridCellCount : Nat
  initialCorridorFace : CorridorFace
  countedTurns : Nat
  reducedTurns : Nat
  activeCorridorFace : CorridorFace
  corridorDial : CorridorBinReport
  grid : List OrbitCorridorGridRead
  slipReads : List OrbitCorridorSlipRead
deriving Repr

def orbitCorridorGridRead (cell : OrbitSlipGridCell) :
    OrbitCorridorGridRead :=
  { lowerStep := cell.lowerStep
    upperStep := cell.upperStep
    selectedNeighborhoodFace := cell.selectedFace
    slipped := cell.slipped
    turnsBefore := cell.orbitBefore
    turnsAfter := cell.orbitAfter
    corridorFaceBefore := CorridorFace.ofTurns cell.orbitBefore
    corridorFaceAfter := CorridorFace.ofTurns cell.orbitAfter
    reducedTurnsAfter := corridorReducedTurns cell.orbitAfter
    residueAfter := cell.residueAfter
    carriedRadiansAfterScaledAt18 := cell.carriedRadiansAfterScaledAt18 }

def orbitCorridorSlipRead (bracket : OrbitSlipBracket) :
    OrbitCorridorSlipRead :=
  { slipIndex := bracket.slipIndex
    lowerStep := bracket.lowerStep
    upperStep := bracket.upperStep
    selectedNeighborhoodFace := bracket.selectedFace
    countedTurns := bracket.slipIndex
    reducedTurns := corridorReducedTurns bracket.slipIndex
    corridorFace := CorridorFace.ofTurns bracket.slipIndex
    lowerRadiansScaledAt18 := bracket.lowerRadiansScaledAt18
    boundaryRadiansScaledAt18 := bracket.slipBoundaryRadiansScaledAt18
    upperRadiansScaledAt18 := bracket.upperRadiansScaledAt18
    bracketWidthRadiansScaledAt18 := bracket.bracketWidthRadiansScaledAt18 }

def orbitCorridorReportFromScan
    (heartbeat : Nat) (scan : OrbitSlipScanReport) : OrbitCorridorReport :=
  let completedDial :=
    if scan.completedOrbitCount = 0 then
      corridorBinReport 0 0
    else
      corridorBinReport 1 scan.completedOrbitCount
  { heartbeat := heartbeat
    targetOrbitCount := scan.targetOrbitCount
    gridCellCount := scan.gridCellCount
    initialCorridorFace := CorridorFace.ofTurns 0
    countedTurns := scan.completedOrbitCount
    reducedTurns := corridorReducedTurns scan.completedOrbitCount
    activeCorridorFace := CorridorFace.ofTurns scan.completedOrbitCount
    corridorDial := completedDial
    grid := scan.grid.map orbitCorridorGridRead
    slipReads := scan.brackets.map orbitCorridorSlipRead }

def defaultOrbitCorridorReport? : Option OrbitCorridorReport :=
  match defaultTwoOrbitSlipScan? with
  | none => none
  | some scan => some (orbitCorridorReportFromScan twoOrbitSlipGridHeartbeat scan)

#eval defaultOrbitCorridorReport?

end Measurement
