import Measurement.Meanwhile56

/- MEANWHILE 57 -- MEASURE ALPHA. The current instrument state is the
Cooper-pair/neutrino same-read after three cranks. The alpha measurement keeps
the raw cranked neutrino reading, removes the reset gravity/spin impulse, and
reports the charge-only alpha together with its inverse read.
-/

namespace Measurement

structure AlphaMeasurementReport where
  name : String
  interpretation : String
  normalization : String
  scale : Nat
  crankCount : Nat
  sameReadAfterThreeCranks : Bool
  rawNeutrinoAlphaScaledAt18 : Nat
  gravitySpinKickScaledAt18 : Int
  resetApplied : Bool
  measuredAlphaScaledAt18 : Nat
  measuredInverseAlphaScaledAt18? : Option Nat
  sourceAlphaScaledAt18 : Nat
  finiteTargetAlphaScaledAt18 : Nat
  finiteTargetInverseAlphaScaledAt18 : Nat
  measuredSourceAbsDiffScaledAt18 : Nat
  measuredFiniteTargetAbsDiffScaledAt18 : Nat
  chargeOnlyBracketLowerScaledAt18 : Nat
  chargeOnlyBracketUpperScaledAt18 : Nat
  chargeOnlyBracketWidthScaledAt18 : Nat
  measuredAlphaInsideChargeOnlyBracket : Bool
  machineEpsilonScaledAt18 : Nat
  measuredWithinMachineEpsilon : Bool
  ownsLimit : Bool
deriving Repr

def alphaInverseReadScaledAt18? (alphaScaledAt18 : Nat) : Option Nat :=
  ratioInverseScaledFloor?
    { numerator := alphaScaledAt18, denominator := pow10 18 } (pow10 18)

def alphaMeasurementReport
    (electron : ElectronAlphaRichardsonReport)
    (reset : NeutrinoGravityMomentumResetReport) :
    AlphaMeasurementReport :=
  let measured := reset.alphaAfterMomentumResetScaledAt18
  let finiteTarget := fineStructureAlphaTarget.scaledFloor (pow10 18)
  { name := "alpha-measurement"
    interpretation :=
      "read alpha from the three-crank Cooper-pair/neutrino state after resetting the gravity/spin momentum"
    normalization := "h = c = 1"
    scale := pow10 18
    crankCount := cooperPairNeutrinoSameCrankCount
    sameReadAfterThreeCranks :=
      cooperPairNeutrinoThreeCrankReport.sameInstrumentReadingAfterCrank
    rawNeutrinoAlphaScaledAt18 :=
      reset.alphaBeforeMomentumResetScaledAt18
    gravitySpinKickScaledAt18 :=
      reset.gravityQuantumMomentumKickScaledAt18
    resetApplied := reset.resetApplied
    measuredAlphaScaledAt18 := measured
    measuredInverseAlphaScaledAt18? := alphaInverseReadScaledAt18? measured
    sourceAlphaScaledAt18 := reset.sourceAlphaScaledAt18
    finiteTargetAlphaScaledAt18 := finiteTarget
    finiteTargetInverseAlphaScaledAt18 :=
      fineStructureInverseFinite.scaledFloor (pow10 18)
    measuredSourceAbsDiffScaledAt18 :=
      reset.remainingUnownedLimitResidueScaledAt18
    measuredFiniteTargetAbsDiffScaledAt18 :=
      natAbsDiff measured finiteTarget
    chargeOnlyBracketLowerScaledAt18 :=
      electron.richardsonBracketLowerScaledAt18
    chargeOnlyBracketUpperScaledAt18 :=
      electron.richardsonBracketUpperScaledAt18
    chargeOnlyBracketWidthScaledAt18 :=
      electron.richardsonBracketWidthScaledAt18
    measuredAlphaInsideChargeOnlyBracket :=
      reset.alphaAfterResetInsideChargeOnlyBracket
    machineEpsilonScaledAt18 :=
      electronMachineEpsilonReport.machineEpsilonScaledAt18
    measuredWithinMachineEpsilon :=
      reset.remainingWithinMachineEpsilon
    ownsLimit := reset.ownsLimit }

def defaultAlphaMeasurementReport? : Option AlphaMeasurementReport :=
  match defaultElectronAlphaRichardsonReport?,
    defaultNeutrinoGravityMomentumResetReport? with
  | some electron, some reset => some (alphaMeasurementReport electron reset)
  | _, _ => none

#eval defaultAlphaMeasurementReport?

end Measurement
