import Measurement.Meanwhile52

/- MEANWHILE 53 -- REMOVE WANDERING SPIN FROM ALPHA. The neutrino channel
identifies spin as the residual exclusion channel. To read a charge-only alpha,
remove the wandering-spin drift introduced by the three-crank neutrino channel
from the latest alpha estimate. The remaining difference from the source alpha is
reported as an unowned limit residue, not silently absorbed.
-/

namespace Measurement

def natMinusInt (value : Nat) : Int -> Nat
  | Int.ofNat n => value - n
  | Int.negSucc n => value + (n + 1)

structure SpinRemovedAlphaReport where
  name : String
  interpretation : String
  electronAlphaEstimateScaledAt18 : Nat
  neutrinoAlphaEstimateScaledAt18 : Nat
  wanderingSpinQuantumGravityScaledAt18 : Int
  wanderingSpinMagnitudeScaledAt18 : Nat
  spinRemovedAlphaScaledAt18 : Nat
  sourceAlphaScaledAt18 : Nat
  spinRemovedSourceAbsDiffScaledAt18 : Nat
  spinRemovedInsideChargeOnlyBracket : Bool
  sourceInsideChargeOnlyBracket : Bool
  spinRemovedWithinMachineEpsilon : Bool
  unownedLimitResidueScaledAt18 : Nat
  ownsLimit : Bool
deriving Repr

def spinRemovedAlphaReport
    (electron : ElectronAlphaRichardsonReport)
    (neutrino : NeutrinoAlphaRichardsonReport) :
    SpinRemovedAlphaReport :=
  let spinDrift :=
    Int.ofNat neutrino.richardsonAlphaEstimateScaledAt18 -
      Int.ofNat electron.richardsonAlphaEstimateScaledAt18
  let spinMagnitude :=
    natAbsDiff neutrino.richardsonAlphaEstimateScaledAt18
      electron.richardsonAlphaEstimateScaledAt18
  let spinRemoved :=
    natMinusInt neutrino.richardsonAlphaEstimateScaledAt18 spinDrift
  let sourceDiff := natAbsDiff spinRemoved electron.sourceAlphaScaledAt18
  { name := "spin-removed-alpha"
    interpretation :=
      "remove neutrino/wandering-spin drift; leave the remaining limit residue unowned"
    electronAlphaEstimateScaledAt18 :=
      electron.richardsonAlphaEstimateScaledAt18
    neutrinoAlphaEstimateScaledAt18 :=
      neutrino.richardsonAlphaEstimateScaledAt18
    wanderingSpinQuantumGravityScaledAt18 := spinDrift
    wanderingSpinMagnitudeScaledAt18 := spinMagnitude
    spinRemovedAlphaScaledAt18 := spinRemoved
    sourceAlphaScaledAt18 := electron.sourceAlphaScaledAt18
    spinRemovedSourceAbsDiffScaledAt18 := sourceDiff
    spinRemovedInsideChargeOnlyBracket :=
      natWithinBracket electron.richardsonBracketLowerScaledAt18 spinRemoved
        electron.richardsonBracketUpperScaledAt18
    sourceInsideChargeOnlyBracket :=
      natWithinBracket electron.richardsonBracketLowerScaledAt18
        electron.sourceAlphaScaledAt18 electron.richardsonBracketUpperScaledAt18
    spinRemovedWithinMachineEpsilon :=
      decide (sourceDiff <= electronMachineEpsilonReport.machineEpsilonScaledAt18)
    unownedLimitResidueScaledAt18 := sourceDiff
    ownsLimit := false }

def defaultSpinRemovedAlphaReport? : Option SpinRemovedAlphaReport :=
  match defaultElectronAlphaRichardsonReport?,
    defaultNeutrinoThreeCrankExperimentReport? with
  | some electron, some neutrinoExperiment =>
      match neutrinoExperiment.richardson with
      | some neutrino => some (spinRemovedAlphaReport electron neutrino)
      | none => none
  | _, _ => none

#eval defaultSpinRemovedAlphaReport?

end Measurement
