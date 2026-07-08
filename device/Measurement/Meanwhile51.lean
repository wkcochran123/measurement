import Measurement.Meanwhile50

/- MEANWHILE 51 -- MEASURING THE SIMULATION. The alpha receipt is a simulated
experiment, but the simulation is not free. Lean's elaborator spends heartbeats
to produce the receipts. This file gathers the already-measured heartbeat
calibrations into one final report, so the simulation has an instrument reading
of its own.
-/

namespace Measurement

def heartbeatStable (a b : Nat) : Bool :=
  decide (a = b ∨ a + 1 = b ∨ b + 1 = a)

structure HeartbeatTriple where
  warmup : Nat
  read2 : Nat
  read3 : Nat
  stable : Bool
deriving Repr

def heartbeatTriple (warmup read2 read3 : Nat) : HeartbeatTriple :=
  { warmup := warmup
    read2 := read2
    read3 := read3
    stable := heartbeatStable read2 read3 }

structure SimulationHeartbeatCalibrationReport where
  instrument : String
  operation : String
  protocol : String
  control : HeartbeatTriple
  base : HeartbeatTriple
  projection : HeartbeatTriple
  recovered : HeartbeatTriple
  decision : HeartbeatTriple
  basePulse : Int
  projectionDelta : Int
  recoverDelta : Int
  decisionDelta : Int
  predictedHeartRate : Int
  targetB2 : HeartbeatTriple
  targetDriver : HeartbeatTriple
  targetDriverDef : HeartbeatTriple
  bindingEnergyB2 : Int
  bindingEnergyDriver : Int
  bindingEnergyDriverDef : Int
deriving Repr

def simulationHeartbeatCalibrationReport :
    SimulationHeartbeatCalibrationReport :=
  { instrument := "Lean elaborator heartbeat counter"
    operation := "elabTerm + whnf"
    protocol := "discard warmup; take read2; check read3 within one heartbeat"
    control := heartbeatTriple g0_warmup g0_r2 g0_r3
    base := heartbeatTriple base_warmup base_r2 base_r3
    projection := heartbeatTriple proj_warmup proj_r2 proj_r3
    recovered := heartbeatTriple recov_warmup recov_r2 recov_r3
    decision := heartbeatTriple dec_warmup dec_r2 dec_r3
    basePulse := basePulse
    projectionDelta := projectionDelta
    recoverDelta := recoverDelta
    decisionDelta := decisionDelta
    predictedHeartRate := predictedHeartRate
    targetB2 := heartbeatTriple tB2_warmup tB2_r2 tB2_r3
    targetDriver := heartbeatTriple tDrv_warmup tDrv_r2 tDrv_r3
    targetDriverDef := heartbeatTriple tDef_warmup tDef_r2 tDef_r3
    bindingEnergyB2 := elabBindingEnergyB2
    bindingEnergyDriver := elabBindingEnergyDriver
    bindingEnergyDriverDef := elabBindingEnergyDriverDef }

structure SimulationMeasurementReport where
  name : String
  heartbeatCalibration : SimulationHeartbeatCalibrationReport
  electronElaborationCharge : ElectronElaborationChargeReport
  electronMachineEpsilon : ElectronMachineEpsilonReport
  orbitCarryEffort : List OrbitCarryPulseReport
  twoOrbitSlipGridHeartbeat : Nat
  twoOrbitSlipGridBracketCount : Nat
  alphaRichardson : Option ElectronAlphaRichardsonReport
deriving Repr

def simulationMeasurementReport : SimulationMeasurementReport :=
  { name := "measuring-the-simulation"
    heartbeatCalibration := simulationHeartbeatCalibrationReport
    electronElaborationCharge := electronElaborationChargeReport
    electronMachineEpsilon := electronMachineEpsilonReport
    orbitCarryEffort := orbitCarryPulseReport
    twoOrbitSlipGridHeartbeat := twoOrbitSlipGridHeartbeat
    twoOrbitSlipGridBracketCount :=
      match twoOrbitSlipGridReceipt.scan with
      | none => 0
      | some scan => scan.bracketCount
    alphaRichardson := defaultElectronAlphaRichardsonReport? }

#eval simulationMeasurementReport

end Measurement
