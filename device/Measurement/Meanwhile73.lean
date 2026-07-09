import Measurement.Meanwhile72

/- MEANWHILE 73 -- SPINOR CONNECTION. Christoffel symbols transport vector
frames. The electron read is spinorial, so the connection must lift through the
two-sheeted spin cover before it can act on the Dirac/Galerkin state.

The finite rule is the same accounting pattern as before: the double cover
takes half of the active Christoffel connection, and the odd half-step residue
is carried. A single vector turn changes the spinor sheet; two vector turns
return it.
-/

namespace Measurement

inductive FiniteSpinorSheet where
  | plus
  | minus
deriving Repr, DecidableEq

def FiniteSpinorSheet.flip : FiniteSpinorSheet -> FiniteSpinorSheet
  | .plus => .minus
  | .minus => .plus

def FiniteSpinorSheet.flipN : Nat -> FiniteSpinorSheet -> FiniteSpinorSheet
  | 0, sheet => sheet
  | n + 1, sheet => flipN n sheet.flip

structure FiniteSpinorState where
  sheet : FiniteSpinorSheet
  spin : Spin
  chirality : Chirality
  diracState : WeakDiracGalerkin.Vec
deriving Repr

def finiteSpinorCoverSheetCount : Nat :=
  qftPhaseCount

def finiteSpinorReturnVectorTurnCount : Nat :=
  finiteSpinorCoverSheetCount * 2

def finiteSpinorAfterOneVectorTurn : FiniteSpinorSheet :=
  FiniteSpinorSheet.flipN finiteSpinorCoverSheetCount.succ .plus

def finiteSpinorAfterTwoVectorTurns : FiniteSpinorSheet :=
  FiniteSpinorSheet.flipN finiteSpinorReturnVectorTurnCount .plus

def finiteSpinorChangesSignAfterOneVectorTurn : Bool :=
  decide (finiteSpinorAfterOneVectorTurn = FiniteSpinorSheet.minus)

def finiteSpinorReturnsAfterTwoVectorTurns : Bool :=
  decide (finiteSpinorAfterTwoVectorTurns = FiniteSpinorSheet.plus)

def finiteSpinorInitialState : FiniteSpinorState :=
  { sheet := .plus
    spin := .up
    chirality := electronResponseChirality
    diracState := diracExperimentReport.spinorState }

def finiteSpinorConnectionHalfFloorScaledAt18 : Nat :=
  finiteChristoffelConnectionTaxScaledAt18 / finiteSpinorCoverSheetCount

def finiteSpinorParityResidueScaledAt18 : Nat :=
  finiteChristoffelConnectionTaxScaledAt18 % finiteSpinorCoverSheetCount

def finiteSpinorConnectionTaxScaledAt18 : Nat :=
  finiteSpinorConnectionHalfFloorScaledAt18 +
    finiteSpinorParityResidueScaledAt18

def finiteSpinorConnectionSignedScaledAt18 : Int :=
  if finiteSpinorInitialState.chirality = Chirality.leftHanded then
    -Int.ofNat finiteSpinorConnectionTaxScaledAt18
  else
    Int.ofNat finiteSpinorConnectionTaxScaledAt18

def finiteSpinorConnectionApplies : Bool :=
  finiteChristoffelReport.connectionApplies &&
    sternGerlachReport.quantizedSpinRead &&
    diracExperimentReport.rawResidualZero &&
    diracExperimentReport.sobolevResidualZero &&
    finiteSpinorChangesSignAfterOneVectorTurn &&
    finiteSpinorReturnsAfterTwoVectorTurns

def finiteSpinorCovariantTaxScaledAt18 : Nat :=
  if finiteSpinorConnectionApplies then
    finiteChristoffelCovariantTaxScaledAt18 +
      finiteSpinorConnectionTaxScaledAt18
  else
    finiteChristoffelCovariantTaxScaledAt18

def finiteSpinorAlphaEstimateScaledAt18 : Nat :=
  qftAlphaScaledAt18 - finiteSpinorCovariantTaxScaledAt18

def finiteSpinorInverseAlphaEstimateScaledAt18? : Option Nat :=
  alphaInverseReadScaledAt18? finiteSpinorAlphaEstimateScaledAt18

def finiteSpinorAlphaLowerScaledAt18 : Nat :=
  finiteSpinorAlphaEstimateScaledAt18 -
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteSpinorAlphaUpperScaledAt18 : Nat :=
  finiteSpinorAlphaEstimateScaledAt18 +
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteSpinorTaxOfQFTAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? finiteSpinorCovariantTaxScaledAt18
    qftAlphaScaledAt18).map scaledFractionToBasisPointsScaledAt18

def finiteSpinorConnectionOfChristoffelScaledAt18? : Option Nat :=
  ratioScaledAt18? finiteSpinorConnectionTaxScaledAt18
    finiteChristoffelConnectionTaxScaledAt18

structure FiniteSpinorConnectionReport where
  name : String
  interpretation : String
  initialState : FiniteSpinorState
  coverSheetCount : Nat
  returnVectorTurnCount : Nat
  afterOneVectorTurn : FiniteSpinorSheet
  afterTwoVectorTurns : FiniteSpinorSheet
  changesSignAfterOneVectorTurn : Bool
  returnsAfterTwoVectorTurns : Bool
  sternGerlachQuantizedSpinRead : Bool
  diracRawResidualZero : Bool
  diracSobolevResidualZero : Bool
  christoffelConnectionTaxScaledAt18 : Nat
  spinorHalfFloorScaledAt18 : Nat
  spinorParityResidueScaledAt18 : Nat
  spinorConnectionTaxScaledAt18 : Nat
  spinorConnectionSignedScaledAt18 : Int
  spinorConnectionApplies : Bool
  christoffelAlphaScaledAt18 : Nat
  christoffelInverseAlphaScaledAt18? : Option Nat
  spinorCovariantTaxScaledAt18 : Nat
  spinorAlphaEstimateScaledAt18 : Nat
  spinorInverseAlphaEstimateScaledAt18? : Option Nat
  lowerAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  upperAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  lowerInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  upperInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  spinorTaxOfQFTAlphaBpsScaledAt18? : Option Nat
  spinorConnectionOfChristoffelScaledAt18? : Option Nat
deriving Repr

def finiteSpinorConnectionReport : FiniteSpinorConnectionReport :=
  { name := "finite-spinor-connection"
    interpretation :=
      "lift the finite Christoffel connection through the two-sheeted spinor cover and carry the odd half-step residue"
    initialState := finiteSpinorInitialState
    coverSheetCount := finiteSpinorCoverSheetCount
    returnVectorTurnCount := finiteSpinorReturnVectorTurnCount
    afterOneVectorTurn := finiteSpinorAfterOneVectorTurn
    afterTwoVectorTurns := finiteSpinorAfterTwoVectorTurns
    changesSignAfterOneVectorTurn :=
      finiteSpinorChangesSignAfterOneVectorTurn
    returnsAfterTwoVectorTurns := finiteSpinorReturnsAfterTwoVectorTurns
    sternGerlachQuantizedSpinRead :=
      sternGerlachReport.quantizedSpinRead
    diracRawResidualZero := diracExperimentReport.rawResidualZero
    diracSobolevResidualZero := diracExperimentReport.sobolevResidualZero
    christoffelConnectionTaxScaledAt18 :=
      finiteChristoffelConnectionTaxScaledAt18
    spinorHalfFloorScaledAt18 :=
      finiteSpinorConnectionHalfFloorScaledAt18
    spinorParityResidueScaledAt18 :=
      finiteSpinorParityResidueScaledAt18
    spinorConnectionTaxScaledAt18 := finiteSpinorConnectionTaxScaledAt18
    spinorConnectionSignedScaledAt18 :=
      finiteSpinorConnectionSignedScaledAt18
    spinorConnectionApplies := finiteSpinorConnectionApplies
    christoffelAlphaScaledAt18 := finiteChristoffelAlphaEstimateScaledAt18
    christoffelInverseAlphaScaledAt18? :=
      finiteChristoffelInverseAlphaEstimateScaledAt18?
    spinorCovariantTaxScaledAt18 := finiteSpinorCovariantTaxScaledAt18
    spinorAlphaEstimateScaledAt18 := finiteSpinorAlphaEstimateScaledAt18
    spinorInverseAlphaEstimateScaledAt18? :=
      finiteSpinorInverseAlphaEstimateScaledAt18?
    lowerAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteSpinorAlphaLowerScaledAt18
    upperAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteSpinorAlphaUpperScaledAt18
    lowerInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteSpinorAlphaLowerScaledAt18
    upperInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteSpinorAlphaUpperScaledAt18
    spinorTaxOfQFTAlphaBpsScaledAt18? :=
      finiteSpinorTaxOfQFTAlphaBpsScaledAt18?
    spinorConnectionOfChristoffelScaledAt18? :=
      finiteSpinorConnectionOfChristoffelScaledAt18? }

#eval finiteSpinorConnectionReport

end Measurement
