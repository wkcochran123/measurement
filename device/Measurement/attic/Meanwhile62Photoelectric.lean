import Measurement.Meanwhile62Mott

/- MEANWHILE 62.3 -- PHOTOELECTRIC EFFECT. The de Broglie certificate gives
the photon as both a wave closure (`p * lambda`) and a discrete energy packet.
In the `h = c = 1` apparatus units, photon energy, frequency, and momentum are
the same scaled read.

The photoelectric read asks whether that photon can pay the local electron
surface work function. The work function is not imported as an exterior
constant: it is the phase-fuzz amplitude already measured at the QFT boundary.
If the photon pays that threshold, the excess is carried as the emitted
electron's kinetic residue. Intensity changes the number of emitted electrons;
it does not change the one-electron stopping read.
-/

namespace Measurement

def photoelectricPhotonEnergyScaledAt18 : Nat :=
  qftPhotonDeBroglieMomentumScaledAt18

def photoelectricPhotonFrequencyScaledAt18 : Nat :=
  photoelectricPhotonEnergyScaledAt18

def photoelectricWorkFunctionScaledAt18 : Nat :=
  qftPhotonPhaseFuzzAmplitudeScaledAt18

def photoelectricThresholdFrequencyScaledAt18 : Nat :=
  photoelectricWorkFunctionScaledAt18

def photoelectricAboveThreshold : Bool :=
  decide
    (photoelectricWorkFunctionScaledAt18 <=
      photoelectricPhotonEnergyScaledAt18)

def photoelectricKineticEnergyScaledAt18 : Nat :=
  if photoelectricAboveThreshold then
    photoelectricPhotonEnergyScaledAt18 -
      photoelectricWorkFunctionScaledAt18
  else
    0

def photoelectricEmittedElectronChargeScaledAt18 : Nat :=
  match defaultQuantumChargeLoopReport? with
  | some report => report.elementaryChargeScaledAt18
  | none => 0

def photoelectricStoppingPotentialScaledAt18? : Option Nat :=
  if photoelectricEmittedElectronChargeScaledAt18 = 0 then
    none
  else
    some
      (photoelectricKineticEnergyScaledAt18 * pow10 18 /
        photoelectricEmittedElectronChargeScaledAt18)

def photoelectricWaveResidualScaledAt18 : Nat :=
  qftPhotonDeBroglieResidualScaledAt18

def photoelectricDiscretePacketPresent : Bool :=
  qftPhotonDeBroglieReport.productClosesOneQuantum &&
    qftPhotonDeBroglieReport.phaseKickAvailable

def photoelectricElectronEmitted : Bool :=
  photoelectricDiscretePacketPresent && photoelectricAboveThreshold

def photoelectricIntensityTotalKineticScaledAt18 (photonCount : Nat) : Nat :=
  if photoelectricElectronEmitted then
    photonCount * photoelectricKineticEnergyScaledAt18
  else
    0

def photoelectricIntensityEmittedElectrons (photonCount : Nat) : Nat :=
  if photoelectricElectronEmitted then photonCount else 0

structure PhotoelectricIntensityRead where
  photonCount : Nat
  emittedElectrons : Nat
  oneElectronKineticEnergyScaledAt18 : Nat
  totalKineticEnergyScaledAt18 : Nat
  stoppingPotentialScaledAt18? : Option Nat
deriving Repr

def photoelectricIntensityRead (photonCount : Nat) :
    PhotoelectricIntensityRead :=
  { photonCount := photonCount
    emittedElectrons := photoelectricIntensityEmittedElectrons photonCount
    oneElectronKineticEnergyScaledAt18 :=
      photoelectricKineticEnergyScaledAt18
    totalKineticEnergyScaledAt18 :=
      photoelectricIntensityTotalKineticScaledAt18 photonCount
    stoppingPotentialScaledAt18? :=
      photoelectricStoppingPotentialScaledAt18? }

def photoelectricIntensityAudit : List PhotoelectricIntensityRead :=
  [photoelectricIntensityRead 1,
    photoelectricIntensityRead 2,
    photoelectricIntensityRead 4]

structure PhotoelectricEffectReport where
  name : String
  interpretation : String
  hSetToOne : Bool
  cSetToOne : Bool
  photonEnergyScaledAt18 : Nat
  photonFrequencyScaledAt18 : Nat
  deBroglieWavelengthScaledAt18 : Nat
  waveProductScaledAt18 : Nat
  waveResidualScaledAt18 : Nat
  discretePacketPresent : Bool
  workFunctionScaledAt18 : Nat
  thresholdFrequencyScaledAt18 : Nat
  aboveThreshold : Bool
  electronEmitted : Bool
  emittedElectronChargeScaledAt18 : Nat
  kineticEnergyScaledAt18 : Nat
  stoppingPotentialScaledAt18? : Option Nat
  kineticEnergyDependsOnIntensity : Bool
  intensityAudit : List PhotoelectricIntensityRead
deriving Repr

def photoelectricEffectReport : PhotoelectricEffectReport :=
  { name := "photoelectric-effect"
    interpretation :=
      "read photon absorption as a threshold event: h nu pays the QFT boundary work function, and the excess leaves as emitted-electron kinetic residue"
    hSetToOne := qftPhotonDeBroglieReport.hSetToOne
    cSetToOne := qftPhotonDeBroglieReport.cSetToOne
    photonEnergyScaledAt18 := photoelectricPhotonEnergyScaledAt18
    photonFrequencyScaledAt18 := photoelectricPhotonFrequencyScaledAt18
    deBroglieWavelengthScaledAt18 :=
      qftPhotonDeBroglieWavelengthScaledAt18
    waveProductScaledAt18 := qftPhotonDeBroglieProductScaledAt18
    waveResidualScaledAt18 := photoelectricWaveResidualScaledAt18
    discretePacketPresent := photoelectricDiscretePacketPresent
    workFunctionScaledAt18 := photoelectricWorkFunctionScaledAt18
    thresholdFrequencyScaledAt18 :=
      photoelectricThresholdFrequencyScaledAt18
    aboveThreshold := photoelectricAboveThreshold
    electronEmitted := photoelectricElectronEmitted
    emittedElectronChargeScaledAt18 :=
      photoelectricEmittedElectronChargeScaledAt18
    kineticEnergyScaledAt18 := photoelectricKineticEnergyScaledAt18
    stoppingPotentialScaledAt18? :=
      photoelectricStoppingPotentialScaledAt18?
    kineticEnergyDependsOnIntensity := false
    intensityAudit := photoelectricIntensityAudit }

#eval photoelectricEffectReport

#eval photoelectricIntensityAudit

end Measurement
