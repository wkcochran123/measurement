import Measurement.Meanwhile71

/- MEANWHILE 72 -- CHRISTOFFEL SYMBOLS. Navier-Stokes gives the finite flow
balance. The Christoffel symbols give the local connection: how the apparatus
frame changes while that flow is transported.

The smooth formula has a `1 / 2` in it. In the finite apparatus that half-step
can leave a parity residue. We do not discard it; the active connection tax is
the ceiling half of the Navier-Stokes flow tax, and the one-unit residue is
reported explicitly.
-/

namespace Measurement

inductive FiniteChartCoordinate where
  | charge
  | mass
  | value
deriving Repr, DecidableEq

structure FiniteMetricGaugeRead where
  coordinate : FiniteChartCoordinate
  diagonalScaledAt18 : Nat
  source : String
deriving Repr

def christoffelMetricGaugeReads : List FiniteMetricGaugeRead :=
  [ { coordinate := .charge
      diagonalScaledAt18 := qftAlphaScaledAt18
      source := "charge horizon alpha" },
    { coordinate := .mass
      diagonalScaledAt18 := qftGravityQuantumScaledAt18
      source := "mass-noise gravity quantum" },
    { coordinate := .value
      diagonalScaledAt18 := finiteNavierStokesPlusFlowMagnitudeScaledAt18
      source := "semiconductor plus-flow" } ]

structure FiniteChristoffelSymbol where
  upper : FiniteChartCoordinate
  lowerLeft : FiniteChartCoordinate
  lowerRight : FiniteChartCoordinate
  coefficientScaledAt18 : Int
  magnitudeScaledAt18 : Nat
  interpretation : String
deriving Repr

def finiteChristoffelHalfFloorScaledAt18 : Nat :=
  finiteNavierStokesTotalTaxScaledAt18 / 2

def finiteChristoffelParityResidueScaledAt18 : Nat :=
  finiteNavierStokesTotalTaxScaledAt18 % 2

def finiteChristoffelConnectionTaxScaledAt18 : Nat :=
  finiteChristoffelHalfFloorScaledAt18 +
    finiteChristoffelParityResidueScaledAt18

def finiteChristoffelCoefficientSignedScaledAt18 : Int :=
  if chiralityRightHandRuleReport.electronFlipsRightHandRule then
    -Int.ofNat finiteChristoffelConnectionTaxScaledAt18
  else
    Int.ofNat finiteChristoffelConnectionTaxScaledAt18

def finiteChristoffelActiveSymbol : FiniteChristoffelSymbol :=
  { upper := .mass
    lowerLeft := .value
    lowerRight := .value
    coefficientScaledAt18 := finiteChristoffelCoefficientSignedScaledAt18
    magnitudeScaledAt18 := finiteChristoffelConnectionTaxScaledAt18
    interpretation :=
      "Gamma^mass_{value,value}: the semiconductor flow bends into the mass/noise frame; electron chirality supplies the sign" }

def finiteChristoffelLowerIndicesSymmetric : Bool :=
  decide
    (finiteChristoffelActiveSymbol.lowerLeft =
      finiteChristoffelActiveSymbol.lowerRight)

def finiteChristoffelTorsionFree : Bool :=
  finiteChristoffelLowerIndicesSymmetric

def finiteChristoffelMetricCompatible : Bool :=
  finiteNavierStokesFlowReport.incompressible &&
    finiteNavierStokesFlowReport.balanceCloses &&
    finiteNavierStokesFlowReport.plusFlowExists &&
    finiteNavierStokesFlowReport.rightHandRuleCloses

def finiteChristoffelConnectionApplies : Bool :=
  finiteChristoffelTorsionFree &&
    finiteChristoffelMetricCompatible &&
    finiteNavierStokesFlowReport.obstructionOn

def finiteChristoffelCovariantTaxScaledAt18 : Nat :=
  if finiteChristoffelConnectionApplies then
    finiteNavierStokesTotalTaxScaledAt18 +
      finiteChristoffelConnectionTaxScaledAt18
  else
    finiteNavierStokesTotalTaxScaledAt18

def finiteChristoffelAlphaEstimateScaledAt18 : Nat :=
  qftAlphaScaledAt18 - finiteChristoffelCovariantTaxScaledAt18

def finiteChristoffelInverseAlphaEstimateScaledAt18? : Option Nat :=
  alphaInverseReadScaledAt18? finiteChristoffelAlphaEstimateScaledAt18

def finiteChristoffelAlphaLowerScaledAt18 : Nat :=
  finiteChristoffelAlphaEstimateScaledAt18 -
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteChristoffelAlphaUpperScaledAt18 : Nat :=
  finiteChristoffelAlphaEstimateScaledAt18 +
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteChristoffelTaxOfQFTAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? finiteChristoffelCovariantTaxScaledAt18
    qftAlphaScaledAt18).map scaledFractionToBasisPointsScaledAt18

def finiteChristoffelConnectionOfNavierStokesTaxScaledAt18? : Option Nat :=
  ratioScaledAt18? finiteChristoffelConnectionTaxScaledAt18
    finiteNavierStokesTotalTaxScaledAt18

structure FiniteChristoffelReport where
  name : String
  interpretation : String
  metricGaugeReads : List FiniteMetricGaugeRead
  activeSymbol : FiniteChristoffelSymbol
  navierStokesTaxScaledAt18 : Nat
  christoffelHalfFloorScaledAt18 : Nat
  christoffelParityResidueScaledAt18 : Nat
  christoffelConnectionTaxScaledAt18 : Nat
  lowerIndicesSymmetric : Bool
  torsionFree : Bool
  metricCompatible : Bool
  connectionApplies : Bool
  ordinaryNavierStokesAlphaScaledAt18 : Nat
  ordinaryNavierStokesInverseAlphaScaledAt18? : Option Nat
  covariantTaxScaledAt18 : Nat
  christoffelAlphaEstimateScaledAt18 : Nat
  christoffelInverseAlphaEstimateScaledAt18? : Option Nat
  lowerAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  upperAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  lowerInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  upperInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  covariantTaxOfQFTAlphaBpsScaledAt18? : Option Nat
  connectionOfNavierStokesTaxScaledAt18? : Option Nat
deriving Repr

def finiteChristoffelReport : FiniteChristoffelReport :=
  { name := "finite-christoffel-symbols"
    interpretation :=
      "read the finite Levi-Civita connection for the Navier-Stokes flow; the active Christoffel coefficient is the carried half-step of the viscous flow tax"
    metricGaugeReads := christoffelMetricGaugeReads
    activeSymbol := finiteChristoffelActiveSymbol
    navierStokesTaxScaledAt18 := finiteNavierStokesTotalTaxScaledAt18
    christoffelHalfFloorScaledAt18 :=
      finiteChristoffelHalfFloorScaledAt18
    christoffelParityResidueScaledAt18 :=
      finiteChristoffelParityResidueScaledAt18
    christoffelConnectionTaxScaledAt18 :=
      finiteChristoffelConnectionTaxScaledAt18
    lowerIndicesSymmetric := finiteChristoffelLowerIndicesSymmetric
    torsionFree := finiteChristoffelTorsionFree
    metricCompatible := finiteChristoffelMetricCompatible
    connectionApplies := finiteChristoffelConnectionApplies
    ordinaryNavierStokesAlphaScaledAt18 :=
      finiteNavierStokesAlphaEstimateScaledAt18
    ordinaryNavierStokesInverseAlphaScaledAt18? :=
      finiteNavierStokesInverseAlphaEstimateScaledAt18?
    covariantTaxScaledAt18 := finiteChristoffelCovariantTaxScaledAt18
    christoffelAlphaEstimateScaledAt18 :=
      finiteChristoffelAlphaEstimateScaledAt18
    christoffelInverseAlphaEstimateScaledAt18? :=
      finiteChristoffelInverseAlphaEstimateScaledAt18?
    lowerAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteChristoffelAlphaLowerScaledAt18
    upperAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteChristoffelAlphaUpperScaledAt18
    lowerInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteChristoffelAlphaLowerScaledAt18
    upperInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteChristoffelAlphaUpperScaledAt18
    covariantTaxOfQFTAlphaBpsScaledAt18? :=
      finiteChristoffelTaxOfQFTAlphaBpsScaledAt18?
    connectionOfNavierStokesTaxScaledAt18? :=
      finiteChristoffelConnectionOfNavierStokesTaxScaledAt18? }

#eval finiteChristoffelReport

end Measurement
