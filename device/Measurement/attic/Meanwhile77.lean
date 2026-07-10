import Measurement.Meanwhile76

/- MEANWHILE 77 -- YANG-MILLS / DIRAC ANTIMATTER MODEL. Antimatter is not a
new hand dial. The device can model it only after two gates close:

* Dirac: the spinor state is an exact weak Galerkin solution and the charge
  conjugate read has the opposite chirality.
* Yang-Mills: the color/flavor/phase sector supplies a nonzero finite
  gauge-curvature budget while color remains a conserved null control.

The anti-Cooper-pair residue from Meanwhile69/70 is then carried as variance
inside the Yang-Mills curvature budget. The alpha center is still the
variational/JFNK center; antimatter widens the modeled envelope rather than
moving the center.
-/

namespace Measurement

inductive FiniteMatterOrientation where
  | matter
  | antimatter
  | neutral
deriving Repr, DecidableEq

structure FiniteDiracChargeConjugateRead where
  name : String
  spinorState : WeakDiracGalerkin.Vec
  electronChargeUnit : Int
  antimatterChargeUnit : Int
  electronChirality : Chirality
  antimatterChirality : Chirality
  rawResidualZero : Bool
  sobolevResidualZero : Bool
  weakLeastActivity : Bool
  chargeConjugationDistinguishes : Bool
  diracChannelCloses : Bool
deriving Repr

def finiteDiracChargeConjugateRead :
    FiniteDiracChargeConjugateRead :=
  { name := "finite-dirac-charge-conjugate"
    spinorState := diracExperimentReport.spinorState
    electronChargeUnit := electronRightHandRuleChargeUnit
    antimatterChargeUnit := positronRightHandRuleChargeUnit
    electronChirality := electronResponseChirality
    antimatterChirality := positronResponseChirality
    rawResidualZero := diracExperimentReport.rawResidualZero
    sobolevResidualZero := diracExperimentReport.sobolevResidualZero
    weakLeastActivity := finiteVariationalWeakLeastActivity
    chargeConjugationDistinguishes :=
      chiralityRightHandRuleReport.mirrorPairDistinguished &&
        chiralityRightHandRuleReport.electronFlipsRightHandRule &&
        chiralityRightHandRuleReport.positronKeepsRightHandRule
    diracChannelCloses :=
      diracExperimentReport.rawResidualZero &&
        diracExperimentReport.sobolevResidualZero &&
        finiteVariationalWeakLeastActivity &&
        chiralityRightHandRuleReport.mirrorPairDistinguished }

structure FiniteYangMillsGaugeRead where
  name : String
  colorCount : Nat
  flavorCount : Nat
  phaseCount : Nat
  sectorCount : Nat
  colorControlNull : Bool
  photonPhaseFuzzesColorFlavor : Bool
  horizonSameFactPreserved : Bool
  curvatureBudgetScaledAt18 : Nat
  curvatureActionScaledAt36 : Nat
  curvatureNonzero : Bool
  yangMillsCloses : Bool
deriving Repr

def finiteYangMillsCurvatureBudgetScaledAt18 : Nat :=
  qftAlphaReport.photonPhaseFuzzAmplitudeScaledAt18

def finiteYangMillsCurvatureActionScaledAt36 : Nat :=
  square finiteYangMillsCurvatureBudgetScaledAt18

def finiteYangMillsCurvatureNonzero : Bool :=
  decide (0 < finiteYangMillsCurvatureBudgetScaledAt18)

def finiteYangMillsCloses : Bool :=
  horizonFlavorColorAlphaReport.colorControlNull &&
    qftAlphaReport.photonPhaseFuzzesColorFlavor &&
    qftAlphaReport.qftPreservesHorizonSameFact &&
    finiteYangMillsCurvatureNonzero

def finiteYangMillsGaugeRead : FiniteYangMillsGaugeRead :=
  { name := "finite-yang-mills-gauge-curvature"
    colorCount := qftAlphaReport.colorCount
    flavorCount := qftAlphaReport.flavorCount
    phaseCount := qftAlphaReport.phaseCount
    sectorCount := qftAlphaReport.sectorCount
    colorControlNull := horizonFlavorColorAlphaReport.colorControlNull
    photonPhaseFuzzesColorFlavor :=
      qftAlphaReport.photonPhaseFuzzesColorFlavor
    horizonSameFactPreserved :=
      qftAlphaReport.qftPreservesHorizonSameFact
    curvatureBudgetScaledAt18 :=
      finiteYangMillsCurvatureBudgetScaledAt18
    curvatureActionScaledAt36 :=
      finiteYangMillsCurvatureActionScaledAt36
    curvatureNonzero := finiteYangMillsCurvatureNonzero
    yangMillsCloses := finiteYangMillsCloses }

def finiteAntimatterFitsYangMillsCurvature : Bool :=
  decide
    (maxSimultaneousAntimatterAmplitudeScaledAt18 <=
      finiteYangMillsCurvatureBudgetScaledAt18)

def finiteAntimatterModelCenterAlphaScaledAt18 : Nat :=
  finiteMechanicsAlphaEstimateScaledAt18

def finiteAntimatterModelLowerAlphaScaledAt18 : Nat :=
  finiteAntimatterModelCenterAlphaScaledAt18 -
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteAntimatterModelUpperAlphaScaledAt18 : Nat :=
  finiteAntimatterModelCenterAlphaScaledAt18 +
    maxSimultaneousAntimatterAmplitudeScaledAt18

def finiteAntimatterModelCloses : Bool :=
  finiteDiracChargeConjugateRead.diracChannelCloses &&
    finiteYangMillsGaugeRead.yangMillsCloses &&
    finiteAntimatterFitsYangMillsCurvature &&
    maxSimultaneousAntimatterReport.antiCooperPairResidueCarried &&
    finiteJFNKMechanicsReport.converged

structure FiniteAntimatterYangMillsDiracReport where
  name : String
  interpretation : String
  diracRead : FiniteDiracChargeConjugateRead
  yangMillsRead : FiniteYangMillsGaugeRead
  antiCooperPairChannelOpen : Bool
  antiCooperPairOccupied : Bool
  antiCooperPairResidueCarried : Bool
  antimatterMemberCount : Nat
  antimatterAmplitudeScaledAt18 : Nat
  antimatterVarianceScaledAt36 : Nat
  antimatterFitsYangMillsCurvature : Bool
  jfnkConverged : Bool
  modeledOrientation : FiniteMatterOrientation
  modelCloses : Bool
  centerAlphaScaledAt18 : Nat
  centerInverseAlphaScaledAt18? : Option Nat
  lowerAlphaWithAntimatterScaledAt18 : Nat
  upperAlphaWithAntimatterScaledAt18 : Nat
  lowerInverseWithAntimatterScaledAt18? : Option Nat
  upperInverseWithAntimatterScaledAt18? : Option Nat
  centerUnchangedByAntimatter : Bool
  ownsContinuumLimit : Bool
deriving Repr

def finiteAntimatterYangMillsDiracReport :
    FiniteAntimatterYangMillsDiracReport :=
  { name := "finite-antimatter-yang-mills-dirac"
    interpretation :=
      "model antimatter as the charge-conjugate Dirac read whose anti-pair variance fits inside the finite Yang-Mills curvature budget"
    diracRead := finiteDiracChargeConjugateRead
    yangMillsRead := finiteYangMillsGaugeRead
    antiCooperPairChannelOpen :=
      maxSimultaneousAntimatterReport.antiCooperPairChannelOpen
    antiCooperPairOccupied :=
      maxSimultaneousAntimatterReport.antiCooperPairOccupied
    antiCooperPairResidueCarried :=
      maxSimultaneousAntimatterReport.antiCooperPairResidueCarried
    antimatterMemberCount := antimatterVarianceMemberCount
    antimatterAmplitudeScaledAt18 :=
      maxSimultaneousAntimatterAmplitudeScaledAt18
    antimatterVarianceScaledAt36 :=
      maxSimultaneousAntimatterVarianceScaledAt36
    antimatterFitsYangMillsCurvature :=
      finiteAntimatterFitsYangMillsCurvature
    jfnkConverged := finiteJFNKMechanicsReport.converged
    modeledOrientation :=
      if finiteAntimatterModelCloses then .antimatter else .neutral
    modelCloses := finiteAntimatterModelCloses
    centerAlphaScaledAt18 := finiteAntimatterModelCenterAlphaScaledAt18
    centerInverseAlphaScaledAt18? :=
      finiteMechanicsInverseAlphaEstimateScaledAt18?
    lowerAlphaWithAntimatterScaledAt18 :=
      finiteAntimatterModelLowerAlphaScaledAt18
    upperAlphaWithAntimatterScaledAt18 :=
      finiteAntimatterModelUpperAlphaScaledAt18
    lowerInverseWithAntimatterScaledAt18? :=
      alphaInverseReadScaledAt18?
        finiteAntimatterModelLowerAlphaScaledAt18
    upperInverseWithAntimatterScaledAt18? :=
      alphaInverseReadScaledAt18?
        finiteAntimatterModelUpperAlphaScaledAt18
    centerUnchangedByAntimatter :=
      decide
        (finiteAntimatterModelCenterAlphaScaledAt18 =
          finiteMechanicsAlphaEstimateScaledAt18)
    ownsContinuumLimit := false }

#eval finiteAntimatterYangMillsDiracReport

end Measurement
