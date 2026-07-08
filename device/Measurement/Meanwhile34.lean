import Measurement.Meanwhile33
import Measurement.WeakDiracGalerkin

/- MEANWHILE 34 -- THE DIRAC EXPERIMENT. Every assembly of the apparatus is a
different physical law. The Dirac assembly is the one that combines:

* the Lorentz bracket from the orbit experiment;
* the two-state spinor forced by undershoot/overshoot;
* the magnetic needle as the gauge/tensor row;
* the weak Sobolev/Galerkin reader as the first-variation test.

The result is not a continuum PDE claim. It is the finite experiment that gives
the Dirac equation: an exact first-order residual whose Sobolev-tested Frechet
variation vanishes on every finite test vector.
-/

namespace Measurement

inductive ApparatusLaw where
  | diracLorentzNeedleOrbit
deriving Repr, DecidableEq

def boolAsInt (b : Bool) : Int :=
  if b then 1 else 0

def regimeIsUndershoot : LorentzOrbitRegime -> Bool
  | .superUnitUndershoot => true
  | _ => false

def regimeIsOvershoot : LorentzOrbitRegime -> Bool
  | .timelikeOvershoot => true
  | _ => false

def diracUndershootComponent : Int :=
  boolAsInt (regimeIsUndershoot lorentzOrbitBracketReport.undershoot.regime)

def diracOvershootComponent : Int :=
  boolAsInt (regimeIsOvershoot lorentzOrbitBracketReport.overshoot.regime)

def diracExperimentState : WeakDiracGalerkin.Vec :=
  [diracUndershootComponent, diracOvershootComponent]

def diracGaugeCoupling : Int :=
  Int.ofNat lorentzOrbitBracketReport.wobbleScaledAt18

def diracExperimentTensor : WeakDiracGalerkin.UniversalTensor :=
  { diracRows :=
      [[1, -1],
       [1,  1],
       [0,  0]]
    tensorRows :=
      [[0, 0],
       [0, 0],
       [diracGaugeCoupling, -diracGaugeCoupling]]
    sobolevRows :=
      [[1, 0, 0],
       [0, 1, 0],
       [0, 0, 1]]
    load :=
      [0, 2, 0] }

def diracExperimentTests : List WeakDiracGalerkin.Vec :=
  [[1, 0, 0],
   [0, 1, 0],
   [0, 0, 1],
   [1, -1, 0],
   [diracGaugeCoupling, 0, -1]]

def vecZero? : WeakDiracGalerkin.Vec -> Bool
  | [] => true
  | x :: xs => (decide (x = 0) : Bool) && vecZero? xs

structure DiracExperimentReport where
  law : ApparatusLaw
  lorentzWobbleScaledAt18 : Nat
  undershootRegime : LorentzOrbitRegime
  boundaryRegime : LorentzOrbitRegime
  overshootRegime : LorentzOrbitRegime
  spinorState : WeakDiracGalerkin.Vec
  gaugeCoupling : Int
  tensor : WeakDiracGalerkin.UniversalTensor
  galerkin : WeakDiracGalerkin.GalerkinReport
  rawResidualZero : Bool
  sobolevResidualZero : Bool
  weakFrechetReads : List Int
deriving Repr

def diracExperimentReport : DiracExperimentReport :=
  let galerkin :=
    WeakDiracGalerkin.report
      diracExperimentTensor diracExperimentState diracExperimentTests
  { law := .diracLorentzNeedleOrbit
    lorentzWobbleScaledAt18 := lorentzOrbitBracketReport.wobbleScaledAt18
    undershootRegime := lorentzOrbitBracketReport.undershoot.regime
    boundaryRegime := lorentzOrbitBracketReport.boundary.regime
    overshootRegime := lorentzOrbitBracketReport.overshoot.regime
    spinorState := diracExperimentState
    gaugeCoupling := diracGaugeCoupling
    tensor := diracExperimentTensor
    galerkin := galerkin
    rawResidualZero := vecZero? galerkin.rawResidual
    sobolevResidualZero := vecZero? galerkin.sobolevResidual
    weakFrechetReads := galerkin.frechetOnTests }

theorem diracExperiment_exactGalerkin :
    WeakDiracGalerkin.ExactGalerkin
      diracExperimentTensor diracExperimentState := by
  rfl

theorem diracExperiment_weakLeastActivity :
    WeakDiracGalerkin.WeakLeastActivity
      diracExperimentTensor diracExperimentState :=
  WeakDiracGalerkin.exactGalerkin_is_weakLeastActivity
    diracExperimentTensor diracExperimentState diracExperiment_exactGalerkin

theorem diracExperiment_rawResidualZero :
    diracExperimentReport.rawResidualZero = true := by
  rfl

theorem diracExperiment_sobolevResidualZero :
    diracExperimentReport.sobolevResidualZero = true := by
  rfl

#eval diracExperimentReport

end Measurement
