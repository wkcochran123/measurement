import Measurement.Meanwhile45

set_option maxRecDepth 2048

/- MEANWHILE 46 -- WATCH THE ELABORATION COST BEND. The selected neighborhood
now rides the orbit. This file keeps that state moving and measures the
elaborator's heartbeat cost at increasing orbit depths.

The carried state uses the adjacent-wobble lattice denominator. Each orbit pass:

  1. advances the PRNG seed,
  2. selects one of the three rational neighborhoods,
  3. projects the selected mean residue onto the wobble lattice,
  4. carries that residue around the orbit,
  5. accumulates the selected variance channel.

The final `register_heart_rate_as` probes are real elaborator heartbeat reads.
-/

namespace Measurement

def projectRatioNumeratorToDenominator
    (targetDenominator : Nat) (q : ApparatusRatio) : Nat :=
  q.numerator * targetDenominator / q.denominator

structure OrbitCarryState where
  steps : Nat
  seed : Nat
  selectedFace : CorridorFace
  latticeDenominator : Nat
  carriedResidueNumerator : Nat
  carriedResidueTurn : ApparatusRatio
  carriedResidueTurnScaledAt18 : Nat
  carriedResidueRadians : ApparatusRatio
  carriedResidueRadiansScaledAt18 : Nat
  varianceRadiansSquaredAccumScaledAt18 : Nat
deriving Repr

def initialOrbitCarryState (latticeDenominator : Nat) : OrbitCarryState :=
  let zeroTurn : ApparatusRatio :=
    { numerator := 0, denominator := latticeDenominator }
  let zeroRadians := zeroTurn.turnsAsRadians
  { steps := 0
    seed := CooperManual.initialSeed
    selectedFace := .charge
    latticeDenominator := latticeDenominator
    carriedResidueNumerator := 0
    carriedResidueTurn := zeroTurn
    carriedResidueTurnScaledAt18 := 0
    carriedResidueRadians := zeroRadians
    carriedResidueRadiansScaledAt18 := 0
    varianceRadiansSquaredAccumScaledAt18 := 0 }

def orbitCarryStep
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport)
    (state : OrbitCarryState) : OrbitCarryState :=
  let report := neighborhoodDeciderReport state.seed aperture read
  let orbitRead := neighborhoodOrbitRead report
  let projectedMeanResidue :=
    projectRatioNumeratorToDenominator state.latticeDenominator
      orbitRead.meanResidueTurn
  let nextResidue :=
    (state.carriedResidueNumerator + projectedMeanResidue) %
      state.latticeDenominator
  let nextTurn : ApparatusRatio :=
    { numerator := nextResidue, denominator := state.latticeDenominator }
  let nextRadians := nextTurn.turnsAsRadians
  { steps := state.steps + 1
    seed := report.seedOut
    selectedFace := report.selectedFace
    latticeDenominator := state.latticeDenominator
    carriedResidueNumerator := nextResidue
    carriedResidueTurn := nextTurn
    carriedResidueTurnScaledAt18 := nextTurn.scaledFloor (pow10 18)
    carriedResidueRadians := nextRadians
    carriedResidueRadiansScaledAt18 := nextRadians.scaledFloor (pow10 18)
    varianceRadiansSquaredAccumScaledAt18 :=
      state.varianceRadiansSquaredAccumScaledAt18 +
        orbitRead.varianceRadiansSquaredScaledAt18 }

def orbitCarryRun
    (aperture : AdjacentWobbleReport)
    (read : ChargeMassNormalizationReport) :
    Nat -> OrbitCarryState -> OrbitCarryState
  | 0, state => state
  | fuel + 1, state =>
      orbitCarryRun aperture read fuel (orbitCarryStep aperture read state)

def defaultOrbitCarryStateAfter? (steps : Nat) : Option OrbitCarryState :=
  defaultAdjacentWobbleReport?.map fun aperture =>
    orbitCarryRun aperture cavendishChargeMassNormalization steps
      (initialOrbitCarryState aperture.latticePeriod)

def orbitCarryProbe (steps : Nat) : Nat :=
  match defaultOrbitCarryStateAfter? steps with
  | none => 0
  | some state =>
      state.carriedResidueRadiansScaledAt18 +
        state.varianceRadiansSquaredAccumScaledAt18

structure OrbitCarryPulseReport where
  steps : Nat
  heartbeat : Nat
  selectedFace : CorridorFace
  carriedResidueNumerator : Nat
  carriedResidueTurnScaledAt18 : Nat
  carriedResidueRadiansScaledAt18 : Nat
  probe : Nat
deriving Repr

def orbitCarryPulseReportAt (steps heartbeat : Nat) : OrbitCarryPulseReport :=
  match defaultOrbitCarryStateAfter? steps with
  | none =>
      { steps := steps
        heartbeat := heartbeat
        selectedFace := .charge
        carriedResidueNumerator := 0
        carriedResidueTurnScaledAt18 := 0
        carriedResidueRadiansScaledAt18 := 0
        probe := 0 }
  | some state =>
      { steps := steps
        heartbeat := heartbeat
        selectedFace := state.selectedFace
        carriedResidueNumerator := state.carriedResidueNumerator
        carriedResidueTurnScaledAt18 := state.carriedResidueTurnScaledAt18
        carriedResidueRadiansScaledAt18 := state.carriedResidueRadiansScaledAt18
        probe := orbitCarryProbe steps }

register_heart_rate_as orbitCarryPulse_warmup (orbitCarryProbe 0)
register_heart_rate_as orbitCarryPulse_000 (orbitCarryProbe 0)
register_heart_rate_as orbitCarryPulse_001 (orbitCarryProbe 1)
register_heart_rate_as orbitCarryPulse_002 (orbitCarryProbe 2)
register_heart_rate_as orbitCarryPulse_004 (orbitCarryProbe 4)
register_heart_rate_as orbitCarryPulse_008 (orbitCarryProbe 8)
register_heart_rate_as orbitCarryPulse_016 (orbitCarryProbe 16)
register_heart_rate_as orbitCarryPulse_032 (orbitCarryProbe 32)
register_heart_rate_as orbitCarryPulse_064 (orbitCarryProbe 64)
register_heart_rate_as orbitCarryPulse_128 (orbitCarryProbe 128)

def orbitCarryPulseReport : List OrbitCarryPulseReport :=
  [ orbitCarryPulseReportAt 0 orbitCarryPulse_000,
    orbitCarryPulseReportAt 1 orbitCarryPulse_001,
    orbitCarryPulseReportAt 2 orbitCarryPulse_002,
    orbitCarryPulseReportAt 4 orbitCarryPulse_004,
    orbitCarryPulseReportAt 8 orbitCarryPulse_008,
    orbitCarryPulseReportAt 16 orbitCarryPulse_016,
    orbitCarryPulseReportAt 32 orbitCarryPulse_032,
    orbitCarryPulseReportAt 64 orbitCarryPulse_064,
    orbitCarryPulseReportAt 128 orbitCarryPulse_128 ]

#eval orbitCarryPulseReport
#eval defaultOrbitCarryStateAfter? 128

end Measurement
