import Measurement.Meanwhile53

/- MEANWHILE 54 -- RESET THE NEUTRINO MOMENTUM. The three-crank neutrino
channel should not leave the gravity impulse stored as charge. Read the
neutrino's signed momentum kick from one gravity quantum, then reset that
neutrino momentum to zero before returning to the charge-only alpha receipt.
-/

namespace Measurement

structure NeutrinoGravityMomentumResetReport where
  name : String
  interpretation : String
  electronAlphaEstimateScaledAt18 : Nat
  neutrinoAlphaEstimateScaledAt18 : Nat
  gravityQuantumMomentumKickScaledAt18 : Int
  gravityQuantumMomentumKickMagnitudeScaledAt18 : Nat
  neutrinoMomentumBeforeGravityScaledAt18 : Int
  neutrinoMomentumAfterGravityScaledAt18 : Int
  neutrinoMomentumAfterResetScaledAt18 : Int
  resetApplied : Bool
  alphaBeforeMomentumResetScaledAt18 : Nat
  alphaAfterMomentumResetScaledAt18 : Nat
  alphaResetMatchesChargeOnly : Bool
  sourceAlphaScaledAt18 : Nat
  sourceInsideChargeOnlyBracket : Bool
  alphaAfterResetInsideChargeOnlyBracket : Bool
  remainingUnownedLimitResidueScaledAt18 : Nat
  remainingWithinMachineEpsilon : Bool
  ownsLimit : Bool
deriving Repr

def neutrinoGravityMomentumResetReport
    (spinRemoved : SpinRemovedAlphaReport) :
    NeutrinoGravityMomentumResetReport :=
  let kick := spinRemoved.wanderingSpinQuantumGravityScaledAt18
  let alphaAfterReset :=
    natMinusInt spinRemoved.neutrinoAlphaEstimateScaledAt18 kick
  let remaining :=
    natAbsDiff alphaAfterReset spinRemoved.sourceAlphaScaledAt18
  { name := "neutrino-gravity-momentum-reset"
    interpretation :=
      "compute the neutrino momentum kick from one gravity quantum; reset that momentum to zero before reading charge-only alpha"
    electronAlphaEstimateScaledAt18 :=
      spinRemoved.electronAlphaEstimateScaledAt18
    neutrinoAlphaEstimateScaledAt18 :=
      spinRemoved.neutrinoAlphaEstimateScaledAt18
    gravityQuantumMomentumKickScaledAt18 := kick
    gravityQuantumMomentumKickMagnitudeScaledAt18 :=
      spinRemoved.wanderingSpinMagnitudeScaledAt18
    neutrinoMomentumBeforeGravityScaledAt18 := 0
    neutrinoMomentumAfterGravityScaledAt18 := kick
    neutrinoMomentumAfterResetScaledAt18 := 0
    resetApplied := true
    alphaBeforeMomentumResetScaledAt18 :=
      spinRemoved.neutrinoAlphaEstimateScaledAt18
    alphaAfterMomentumResetScaledAt18 := alphaAfterReset
    alphaResetMatchesChargeOnly :=
      decide (alphaAfterReset = spinRemoved.electronAlphaEstimateScaledAt18)
    sourceAlphaScaledAt18 := spinRemoved.sourceAlphaScaledAt18
    sourceInsideChargeOnlyBracket :=
      spinRemoved.sourceInsideChargeOnlyBracket
    alphaAfterResetInsideChargeOnlyBracket :=
      spinRemoved.spinRemovedInsideChargeOnlyBracket
    remainingUnownedLimitResidueScaledAt18 := remaining
    remainingWithinMachineEpsilon :=
      decide (remaining <= electronMachineEpsilonReport.machineEpsilonScaledAt18)
    ownsLimit := false }

def defaultNeutrinoGravityMomentumResetReport? :
    Option NeutrinoGravityMomentumResetReport :=
  defaultSpinRemovedAlphaReport?.map neutrinoGravityMomentumResetReport

#eval defaultNeutrinoGravityMomentumResetReport?

end Measurement
