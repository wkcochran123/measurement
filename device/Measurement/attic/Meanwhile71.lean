import Measurement.Meanwhile70

/- MEANWHILE 71 -- FINITE NAVIER-STOKES FLOW TAX. The apparatus already has a
finite Navier-Stokes-shaped residue in Episode75. This file wires that residue
into the physical chain: semiconductor `+` flow supplies the measured current
denominator, chirality supplies the orientation convention, and the visible
mass-noise quantum supplies the dissipative unit.

This is not continuum Navier-Stokes. It is the finite weak-flow read that the
device can actually compute: incompressible balance, nonzero viscous boundary
flux, and the induced alpha estimate after charging that flux against the
measured flow.
-/

namespace Measurement

inductive FiniteFlowSignal where
  | off
  | on
deriving Repr, DecidableEq

structure FiniteWeakNavierStokesResidue where
  transport : Int
  pressure : Int
  viscousBoundaryFlux : Int
  boundaryForcing : Int
  divergence : Int
  obstructionSignal : FiniteFlowSignal
  balanceCloses : Bool
  incompressible : Bool
deriving Repr

def threeRungFiniteWeakNavierStokesResidue :
    FiniteWeakNavierStokesResidue :=
  { transport := 0
    pressure := 0
    viscousBoundaryFlux := -1
    boundaryForcing := -1
    divergence := 0
    obstructionSignal := .on
    balanceCloses := true
    incompressible := true }

def finiteFlowSignalIsOn : FiniteFlowSignal -> Bool
  | .on => true
  | .off => false

def finiteNavierStokesTransportMagnitude : Nat :=
  intMagnitude threeRungFiniteWeakNavierStokesResidue.transport

def finiteNavierStokesPressureMagnitude : Nat :=
  intMagnitude threeRungFiniteWeakNavierStokesResidue.pressure

def finiteNavierStokesViscousFluxMagnitude : Nat :=
  intMagnitude threeRungFiniteWeakNavierStokesResidue.viscousBoundaryFlux

def finiteNavierStokesBoundaryForcingMagnitude : Nat :=
  intMagnitude threeRungFiniteWeakNavierStokesResidue.boundaryForcing

def finiteNavierStokesBalanceCloses : Bool :=
  threeRungFiniteWeakNavierStokesResidue.balanceCloses

def finiteNavierStokesIncompressible : Bool :=
  threeRungFiniteWeakNavierStokesResidue.incompressible

def finiteNavierStokesObstructionOn : Bool :=
  finiteFlowSignalIsOn
    threeRungFiniteWeakNavierStokesResidue.obstructionSignal

def finiteNavierStokesPlusFlowMagnitudeScaledAt18 : Nat :=
  intMagnitude semiconductorTotalPositiveFlowScaledAt18

def finiteNavierStokesFlowDenominatorScaledAt18 : Nat :=
  Nat.max 1 finiteNavierStokesPlusFlowMagnitudeScaledAt18

def finiteNavierStokesFlowUnitTaxScaledAt18 : Nat :=
  qftGravityQuantumScaledAt18 * pow10 18 /
    finiteNavierStokesFlowDenominatorScaledAt18

def finiteNavierStokesViscousFlowTaxScaledAt18 : Nat :=
  finiteNavierStokesFlowUnitTaxScaledAt18 *
    finiteNavierStokesViscousFluxMagnitude

def finiteNavierStokesCurvatureTaxScaledAt18 : Nat :=
  qftGravityQuantumScaledAt18 * smallAngleCubicCorrectionScaledAt36 /
    pow10 36

def finiteNavierStokesTotalTaxScaledAt18 : Nat :=
  finiteNavierStokesViscousFlowTaxScaledAt18 +
    finiteNavierStokesCurvatureTaxScaledAt18

def finiteNavierStokesAlphaEstimateScaledAt18 : Nat :=
  qftAlphaScaledAt18 - finiteNavierStokesTotalTaxScaledAt18

def finiteNavierStokesInverseAlphaEstimateScaledAt18? : Option Nat :=
  alphaInverseReadScaledAt18? finiteNavierStokesAlphaEstimateScaledAt18

def finiteNavierStokesAlphaLowerScaledAt18 : Nat :=
  finiteNavierStokesAlphaEstimateScaledAt18 -
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteNavierStokesAlphaUpperScaledAt18 : Nat :=
  finiteNavierStokesAlphaEstimateScaledAt18 +
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteNavierStokesTaxOfQFTAlphaBpsScaledAt18? : Option Nat :=
  (ratioScaledAt18? finiteNavierStokesTotalTaxScaledAt18
    qftAlphaScaledAt18).map scaledFractionToBasisPointsScaledAt18

def finiteNavierStokesTaxOfAntimatterEnvelopeScaledAt18? : Option Nat :=
  ratioScaledAt18? finiteNavierStokesTotalTaxScaledAt18
    maxSimultaneousAntimatterAmplitudeScaledAt18

structure FiniteNavierStokesFlowReport where
  name : String
  interpretation : String
  transport : Int
  pressure : Int
  viscousBoundaryFlux : Int
  boundaryForcing : Int
  divergence : Int
  transportMagnitude : Nat
  pressureMagnitude : Nat
  viscousFluxMagnitude : Nat
  boundaryForcingMagnitude : Nat
  balanceCloses : Bool
  incompressible : Bool
  obstructionOn : Bool
  plusFlowExists : Bool
  plusFlowMagnitudeScaledAt18 : Nat
  rightHandRuleCloses : Bool
  smallAngleLinearRegime : Bool
  smallAngleCurvatureScaledAt36 : Nat
  gravityQuantumScaledAt18 : Nat
  flowUnitTaxScaledAt18 : Nat
  viscousFlowTaxScaledAt18 : Nat
  curvatureTaxScaledAt18 : Nat
  totalNavierStokesTaxScaledAt18 : Nat
  qftAlphaScaledAt18 : Nat
  navierStokesAlphaEstimateScaledAt18 : Nat
  navierStokesInverseAlphaEstimateScaledAt18? : Option Nat
  lowerAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  upperAlphaWithAntimatterEnvelopeScaledAt18 : Nat
  lowerInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  upperInverseWithAntimatterEnvelopeScaledAt18? : Option Nat
  taxOfQFTAlphaBpsScaledAt18? : Option Nat
  taxOfAntimatterEnvelopeScaledAt18? : Option Nat
deriving Repr

def finiteNavierStokesFlowReport : FiniteNavierStokesFlowReport :=
  { name := "finite-navier-stokes-flow-tax"
    interpretation :=
      "charge the Episode75 finite incompressible viscous boundary flux against the measured semiconductor plus-flow"
    transport := threeRungFiniteWeakNavierStokesResidue.transport
    pressure := threeRungFiniteWeakNavierStokesResidue.pressure
    viscousBoundaryFlux :=
      threeRungFiniteWeakNavierStokesResidue.viscousBoundaryFlux
    boundaryForcing :=
      threeRungFiniteWeakNavierStokesResidue.boundaryForcing
    divergence := threeRungFiniteWeakNavierStokesResidue.divergence
    transportMagnitude := finiteNavierStokesTransportMagnitude
    pressureMagnitude := finiteNavierStokesPressureMagnitude
    viscousFluxMagnitude := finiteNavierStokesViscousFluxMagnitude
    boundaryForcingMagnitude := finiteNavierStokesBoundaryForcingMagnitude
    balanceCloses := finiteNavierStokesBalanceCloses
    incompressible := finiteNavierStokesIncompressible
    obstructionOn := finiteNavierStokesObstructionOn
    plusFlowExists := semiconductorPlusFlowReport.plusFlowExists
    plusFlowMagnitudeScaledAt18 :=
      finiteNavierStokesPlusFlowMagnitudeScaledAt18
    rightHandRuleCloses :=
      chiralityRightHandRuleReport.chiralityCertificate
    smallAngleLinearRegime :=
      smallAngleApproximationReport.pendulumLinearRegime
    smallAngleCurvatureScaledAt36 := smallAngleCubicCorrectionScaledAt36
    gravityQuantumScaledAt18 := qftGravityQuantumScaledAt18
    flowUnitTaxScaledAt18 := finiteNavierStokesFlowUnitTaxScaledAt18
    viscousFlowTaxScaledAt18 :=
      finiteNavierStokesViscousFlowTaxScaledAt18
    curvatureTaxScaledAt18 := finiteNavierStokesCurvatureTaxScaledAt18
    totalNavierStokesTaxScaledAt18 :=
      finiteNavierStokesTotalTaxScaledAt18
    qftAlphaScaledAt18 := qftAlphaScaledAt18
    navierStokesAlphaEstimateScaledAt18 :=
      finiteNavierStokesAlphaEstimateScaledAt18
    navierStokesInverseAlphaEstimateScaledAt18? :=
      finiteNavierStokesInverseAlphaEstimateScaledAt18?
    lowerAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteNavierStokesAlphaLowerScaledAt18
    upperAlphaWithAntimatterEnvelopeScaledAt18 :=
      finiteNavierStokesAlphaUpperScaledAt18
    lowerInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteNavierStokesAlphaLowerScaledAt18
    upperInverseWithAntimatterEnvelopeScaledAt18? :=
      alphaInverseReadScaledAt18? finiteNavierStokesAlphaUpperScaledAt18
    taxOfQFTAlphaBpsScaledAt18? :=
      finiteNavierStokesTaxOfQFTAlphaBpsScaledAt18?
    taxOfAntimatterEnvelopeScaledAt18? :=
      finiteNavierStokesTaxOfAntimatterEnvelopeScaledAt18? }

#eval finiteNavierStokesFlowReport

end Measurement
