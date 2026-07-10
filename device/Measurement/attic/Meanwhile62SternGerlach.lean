import Measurement.Meanwhile62

/- MEANWHILE 62.1 -- STERN-GERLACH SPIN SPLIT. The de Broglie certificate says
the photon boundary has both a wave closure and a discrete phase kick. Before
photoelectric absorption consumes that boundary, the apparatus can use a
magnetic gradient to ask for spin projection.

Stern-Gerlach is the approximation that turns a continuous-looking magnetic
interaction into two separated labels. The magnetic gradient is read from the
Meissner photon field over the de Broglie wavelength. The spin projection has
two outcomes, up and down, so the apparatus records two beams and no middle
beam.
-/

namespace Measurement

inductive SternGerlachBeam where
  | upper
  | lower
deriving Repr, DecidableEq

def sternGerlachMagneticGradientScaledAt18 : Nat :=
  if qftPhotonDeBroglieWavelengthScaledAt18 = 0 then
    0
  else
    magneticPhotonExchangeReport.incident.fieldScaledAt18 * pow10 18 /
      qftPhotonDeBroglieWavelengthScaledAt18

def sternGerlachSpinProjectionMagnitudeScaledAt18 : Nat :=
  qftPhotonDeBroglieActionQuantumScaledAt18 / qftPhaseCount

def sternGerlachDeflectionMagnitudeScaledAt18 : Nat :=
  sternGerlachMagneticGradientScaledAt18 / qftPhaseCount

def sternGerlachBeamForSpin : Spin -> SternGerlachBeam
  | .up => .upper
  | .down => .lower

def sternGerlachProjectionSignedScaledAt18 : Spin -> Int
  | .up => Int.ofNat sternGerlachSpinProjectionMagnitudeScaledAt18
  | .down => -Int.ofNat sternGerlachSpinProjectionMagnitudeScaledAt18

def sternGerlachDeflectionSignedScaledAt18 : Spin -> Int
  | .up => Int.ofNat sternGerlachDeflectionMagnitudeScaledAt18
  | .down => -Int.ofNat sternGerlachDeflectionMagnitudeScaledAt18

def sternGerlachBeamSeparationScaledAt18 : Nat :=
  2 * sternGerlachDeflectionMagnitudeScaledAt18

structure SternGerlachBeamRead where
  spin : Spin
  beam : SternGerlachBeam
  projectionSignedScaledAt18 : Int
  deflectionSignedScaledAt18 : Int
  deBrogliePhaseAvailable : Bool
  magneticGradientScaledAt18 : Nat
deriving Repr

def sternGerlachBeamRead (spin : Spin) : SternGerlachBeamRead :=
  { spin := spin
    beam := sternGerlachBeamForSpin spin
    projectionSignedScaledAt18 :=
      sternGerlachProjectionSignedScaledAt18 spin
    deflectionSignedScaledAt18 :=
      sternGerlachDeflectionSignedScaledAt18 spin
    deBrogliePhaseAvailable := qftPhotonDeBroglieReport.phaseKickAvailable
    magneticGradientScaledAt18 := sternGerlachMagneticGradientScaledAt18 }

def sternGerlachBeamReads : List SternGerlachBeamRead :=
  [sternGerlachBeamRead .up, sternGerlachBeamRead .down]

def sternGerlachMagneticGradientAvailable : Bool :=
  magneticPhotonExchangeReport.photonMediatorPresent &&
    qftPhotonDeBroglieReport.phaseKickAvailable &&
    decide (0 < sternGerlachMagneticGradientScaledAt18)

def sternGerlachTwoBeamSplit : Bool :=
  decide (sternGerlachBeamReads.length = qftPhaseCount) &&
    decide
      (sternGerlachDeflectionSignedScaledAt18 .up =
        -sternGerlachDeflectionSignedScaledAt18 .down)

def sternGerlachNoMiddleBeam : Bool :=
  decide (0 < sternGerlachDeflectionMagnitudeScaledAt18) &&
    decide (sternGerlachBeamForSpin .up ≠ sternGerlachBeamForSpin .down)

def sternGerlachQuantizedSpinRead : Bool :=
  sternGerlachMagneticGradientAvailable &&
    sternGerlachTwoBeamSplit &&
    sternGerlachNoMiddleBeam

structure SternGerlachReport where
  name : String
  interpretation : String
  afterDeBroglie : Bool
  hSetToOne : Bool
  cSetToOne : Bool
  photonMomentumScaledAt18 : Nat
  deBroglieWavelengthScaledAt18 : Nat
  deBrogliePhaseAvailable : Bool
  magneticFieldScaledAt18 : Nat
  magneticGradientScaledAt18 : Nat
  spinProjectionMagnitudeScaledAt18 : Nat
  deflectionMagnitudeScaledAt18 : Nat
  beamSeparationScaledAt18 : Nat
  beams : List SternGerlachBeamRead
  twoBeamSplit : Bool
  noMiddleBeam : Bool
  quantizedSpinRead : Bool
deriving Repr

def sternGerlachReport : SternGerlachReport :=
  { name := "stern-gerlach-spin-split"
    interpretation :=
      "the de Broglie phase enters a magnetic gradient and resolves spin as two separated beams, not a continuous middle value"
    afterDeBroglie := qftPhotonDeBroglieReport.phaseKickAvailable
    hSetToOne := qftPhotonDeBroglieReport.hSetToOne
    cSetToOne := qftPhotonDeBroglieReport.cSetToOne
    photonMomentumScaledAt18 := qftPhotonDeBroglieMomentumScaledAt18
    deBroglieWavelengthScaledAt18 :=
      qftPhotonDeBroglieWavelengthScaledAt18
    deBrogliePhaseAvailable := qftPhotonDeBroglieReport.phaseKickAvailable
    magneticFieldScaledAt18 :=
      magneticPhotonExchangeReport.incident.fieldScaledAt18
    magneticGradientScaledAt18 :=
      sternGerlachMagneticGradientScaledAt18
    spinProjectionMagnitudeScaledAt18 :=
      sternGerlachSpinProjectionMagnitudeScaledAt18
    deflectionMagnitudeScaledAt18 :=
      sternGerlachDeflectionMagnitudeScaledAt18
    beamSeparationScaledAt18 := sternGerlachBeamSeparationScaledAt18
    beams := sternGerlachBeamReads
    twoBeamSplit := sternGerlachTwoBeamSplit
    noMiddleBeam := sternGerlachNoMiddleBeam
    quantizedSpinRead := sternGerlachQuantizedSpinRead }

#eval sternGerlachReport

end Measurement
