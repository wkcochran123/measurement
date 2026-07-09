import Measurement.Meanwhile73

/- MEANWHILE 74 -- VARIATIONAL CALCULUS. The spinor connection tells us how
the transported electron state turns. Variational calculus asks whether that
transported state is stationary under the finite Sobolev/Galerkin tests.

The first variation is already the weak Dirac/Galerkin Frechet read. In this
finite apparatus it vanishes exactly. The next payable term is therefore the
second variation: the curvature/stability cost needed to keep the spinor
connection on the stationary branch.
-/

namespace Measurement

inductive FiniteVariationalOrder where
  | action
  | firstVariation
  | secondVariation
deriving Repr, DecidableEq

structure FiniteVariationalProbe where
  order : FiniteVariationalOrder
  name : String
  test : WeakDiracGalerkin.Vec
  frechetRead : Int
  interpretation : String
deriving Repr

def finiteVariationalIntListAllZero : List Int -> Bool
  | [] => true
  | x :: xs => (decide (x = 0) : Bool) &&
      finiteVariationalIntListAllZero xs

def finiteVariationalIntListMagnitudeSum : List Int -> Nat
  | [] => 0
  | x :: xs => intMagnitude x +
      finiteVariationalIntListMagnitudeSum xs

def finiteVariationalActionValue : Int :=
  WeakDiracGalerkin.sobolevNormSq
    diracExperimentTensor diracExperimentState

def finiteVariationalActivityMagnitude : Nat :=
  intMagnitude finiteVariationalActionValue

def finiteVariationalRawResidual : WeakDiracGalerkin.Vec :=
  WeakDiracGalerkin.rawTensorResidual
    diracExperimentTensor diracExperimentState

def finiteVariationalSobolevResidual : WeakDiracGalerkin.Vec :=
  WeakDiracGalerkin.sobolevResidual
    diracExperimentTensor diracExperimentState

def finiteVariationalFirstFrechetReads : List Int :=
  diracExperimentTests.map (fun test =>
    WeakDiracGalerkin.firstFrechetVariation
      diracExperimentTensor diracExperimentState test)

def finiteVariationalFirstVariationVanishes : Bool :=
  finiteVariationalIntListAllZero finiteVariationalFirstFrechetReads

def finiteVariationalFirstVariationResidualScaledAt18 : Nat :=
  finiteVariationalIntListMagnitudeSum finiteVariationalFirstFrechetReads

def finiteVariationalWeakLeastActivity : Bool :=
  diracExperimentReport.rawResidualZero &&
    diracExperimentReport.sobolevResidualZero &&
    finiteVariationalFirstVariationVanishes

def finiteVariationalEulerLagrangeCloses : Bool :=
  finiteVariationalWeakLeastActivity &&
    finiteSpinorConnectionReport.spinorConnectionApplies

def finiteVariationalSecondVariationFloorScaledAt18 : Nat :=
  finiteSpinorConnectionTaxScaledAt18 / finiteSpinorCoverSheetCount

def finiteVariationalSecondVariationResidueScaledAt18 : Nat :=
  finiteSpinorConnectionTaxScaledAt18 % finiteSpinorCoverSheetCount

def finiteVariationalSecondVariationCurvatureTaxScaledAt18 : Nat :=
  finiteVariationalSecondVariationFloorScaledAt18 +
    finiteVariationalSecondVariationResidueScaledAt18

def finiteVariationalSecondVariationApplies : Bool :=
  finiteVariationalEulerLagrangeCloses &&
    decide (finiteVariationalFirstVariationResidualScaledAt18 = 0)

def finiteVariationalSecondVariationPositive : Bool :=
  decide (0 < finiteVariationalSecondVariationCurvatureTaxScaledAt18)

def finiteVariationalEulerLagrangeMinimizesActivity : Bool :=
  finiteVariationalEulerLagrangeCloses &&
    finiteVariationalSecondVariationApplies &&
    finiteVariationalSecondVariationPositive &&
    decide (finiteVariationalActivityMagnitude = 0)

def finiteVariationalTotalTaxScaledAt18 : Nat :=
  if finiteVariationalSecondVariationApplies then
    finiteSpinorCovariantTaxScaledAt18 +
      finiteVariationalSecondVariationCurvatureTaxScaledAt18
  else
    finiteSpinorCovariantTaxScaledAt18 +
      finiteVariationalFirstVariationResidualScaledAt18

def finiteVariationalAlphaEstimateScaledAt18 : Nat :=
  qftAlphaScaledAt18 - finiteVariationalTotalTaxScaledAt18

def finiteVariationalInverseAlphaEstimateScaledAt18? : Option Nat :=
  alphaInverseReadScaledAt18? finiteVariationalAlphaEstimateScaledAt18

def finiteVariationalAlphaLowerScaledAt18 : Nat :=
  finiteVariationalAlphaEstimateScaledAt18 -
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteVariationalAlphaUpperScaledAt18 : Nat :=
  finiteVariationalAlphaEstimateScaledAt18 +
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteVariationalTaxOfQFTAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? finiteVariationalTotalTaxScaledAt18
    qftAlphaScaledAt18).map scaledFractionToBasisPointsScaledAt18

def finiteVariationalSecondVariationOfSpinorScaledAt18? : Option Nat :=
  ratioScaledAt18? finiteVariationalSecondVariationCurvatureTaxScaledAt18
    finiteSpinorConnectionTaxScaledAt18

def finiteVariationalProbes : List FiniteVariationalProbe :=
  [ { order := .firstVariation
      name := "mass-basis"
      test := [1, 0, 0]
      frechetRead :=
        WeakDiracGalerkin.firstFrechetVariation
          diracExperimentTensor diracExperimentState [1, 0, 0]
      interpretation := "basis variation in the mass/Sobolev row" },
    { order := .firstVariation
      name := "charge-basis"
      test := [0, 1, 0]
      frechetRead :=
        WeakDiracGalerkin.firstFrechetVariation
          diracExperimentTensor diracExperimentState [0, 1, 0]
      interpretation := "basis variation in the charge/Sobolev row" },
    { order := .firstVariation
      name := "value-basis"
      test := [0, 0, 1]
      frechetRead :=
        WeakDiracGalerkin.firstFrechetVariation
          diracExperimentTensor diracExperimentState [0, 0, 1]
      interpretation := "basis variation in the tensor/gauge row" },
    { order := .secondVariation
      name := "spinor-curvature"
      test := [1, -1, 0]
      frechetRead :=
        WeakDiracGalerkin.firstFrechetVariation
          diracExperimentTensor diracExperimentState [1, -1, 0]
      interpretation :=
        "stationary first variation; the carried half-spinor connection is the payable curvature term" } ]

structure FiniteVariationalCalculusReport where
  name : String
  interpretation : String
  actionValue : Int
  activityMagnitude : Nat
  rawResidual : WeakDiracGalerkin.Vec
  sobolevResidual : WeakDiracGalerkin.Vec
  firstFrechetReads : List Int
  firstVariationVanishes : Bool
  firstVariationResidualScaledAt18 : Nat
  weakLeastActivity : Bool
  eulerLagrangeCloses : Bool
  probes : List FiniteVariationalProbe
  spinorConnectionTaxScaledAt18 : Nat
  secondVariationFloorScaledAt18 : Nat
  secondVariationResidueScaledAt18 : Nat
  secondVariationCurvatureTaxScaledAt18 : Nat
  secondVariationApplies : Bool
  secondVariationPositive : Bool
  eulerLagrangeMinimizesActivity : Bool
  spinorAlphaScaledAt18 : Nat
  spinorInverseAlphaScaledAt18? : Option Nat
  totalVariationalTaxScaledAt18 : Nat
  variationalAlphaEstimateScaledAt18 : Nat
  variationalInverseAlphaEstimateScaledAt18? : Option Nat
  lowerAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  upperAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  lowerInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  upperInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  totalTaxOfQFTAlphaBpsScaledAt18? : Option Nat
  secondVariationOfSpinorScaledAt18? : Option Nat
deriving Repr

def finiteVariationalCalculusReport :
    FiniteVariationalCalculusReport :=
  { name := "finite-variational-calculus"
    interpretation :=
      "read the weak Dirac/Galerkin Frechet derivative; since the first variation vanishes, charge the spinor second-variation curvature"
    actionValue := finiteVariationalActionValue
    activityMagnitude := finiteVariationalActivityMagnitude
    rawResidual := finiteVariationalRawResidual
    sobolevResidual := finiteVariationalSobolevResidual
    firstFrechetReads := finiteVariationalFirstFrechetReads
    firstVariationVanishes := finiteVariationalFirstVariationVanishes
    firstVariationResidualScaledAt18 :=
      finiteVariationalFirstVariationResidualScaledAt18
    weakLeastActivity := finiteVariationalWeakLeastActivity
    eulerLagrangeCloses := finiteVariationalEulerLagrangeCloses
    probes := finiteVariationalProbes
    spinorConnectionTaxScaledAt18 := finiteSpinorConnectionTaxScaledAt18
    secondVariationFloorScaledAt18 :=
      finiteVariationalSecondVariationFloorScaledAt18
    secondVariationResidueScaledAt18 :=
      finiteVariationalSecondVariationResidueScaledAt18
    secondVariationCurvatureTaxScaledAt18 :=
      finiteVariationalSecondVariationCurvatureTaxScaledAt18
    secondVariationApplies := finiteVariationalSecondVariationApplies
    secondVariationPositive := finiteVariationalSecondVariationPositive
    eulerLagrangeMinimizesActivity :=
      finiteVariationalEulerLagrangeMinimizesActivity
    spinorAlphaScaledAt18 := finiteSpinorAlphaEstimateScaledAt18
    spinorInverseAlphaScaledAt18? :=
      finiteSpinorInverseAlphaEstimateScaledAt18?
    totalVariationalTaxScaledAt18 := finiteVariationalTotalTaxScaledAt18
    variationalAlphaEstimateScaledAt18 :=
      finiteVariationalAlphaEstimateScaledAt18
    variationalInverseAlphaEstimateScaledAt18? :=
      finiteVariationalInverseAlphaEstimateScaledAt18?
    lowerAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteVariationalAlphaLowerScaledAt18
    upperAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteVariationalAlphaUpperScaledAt18
    lowerInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteVariationalAlphaLowerScaledAt18
    upperInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteVariationalAlphaUpperScaledAt18
    totalTaxOfQFTAlphaBpsScaledAt18? :=
      finiteVariationalTaxOfQFTAlphaBpsScaledAt18?
    secondVariationOfSpinorScaledAt18? :=
      finiteVariationalSecondVariationOfSpinorScaledAt18? }

theorem finiteVariational_weakLeastActivity :
    WeakDiracGalerkin.WeakLeastActivity
      diracExperimentTensor diracExperimentState :=
  diracExperiment_weakLeastActivity

#eval finiteVariationalCalculusReport

end Measurement
