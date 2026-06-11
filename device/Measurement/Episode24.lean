import Measurement.Episode23

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 24__: _Cubic Euler-Lagrange Support_

Episode23 packaged a partitioned `R -> R` approximation.  This episode
derives the finite Euler-Lagrange equations for a cubic segment.

A cubic has four nodes.  The two boundary nodes are held fixed.  The two
middle nodes are supported by finite elephants, and each finite elephant is
equipped with its real partition.  The Euler-Lagrange equations are the two
middle-node residual equations, one over each elephant-supported candidate
multiset.

The four-node cost has one more bead: if both middle nodes vary at once, the
middle segment contributes a mixed coupling term.  The one-coordinate
variation theorems identify the left and right residuals exactly; the coupled
variation theorem keeps the mixed term visible.

Stated formally:
supported left/right residuals plus solved mixed coupling imply zero coupled
cubic difference.

Claimed by interpretation:
the cubic spline satisfies the finite middle-node equations on represented
data support.

Residue left:
the mixed coupling must be separately solved or bounded.
-/

structure CubicGaugePath where
  source : Bullshit
  middleLeft : Bullshit
  middleRight : Bullshit
  target : Bullshit

namespace CubicGaugePath

def leftFinitePath (path : CubicGaugePath) : FiniteGaugePath where
  source := path.source
  slip := path.middleLeft
  target := path.middleRight

def rightFinitePath (path : CubicGaugePath) : FiniteGaugePath where
  source := path.middleLeft
  slip := path.middleRight
  target := path.target

def cubicCost (action : FiniteGaugeAction) (path : CubicGaugePath) : Nat :=
  action.segmentCost path.source path.middleLeft +
    action.segmentCost path.middleLeft path.middleRight +
      action.segmentCost path.middleRight path.target

def withMiddleLeft
    (path : CubicGaugePath) (middleLeft : Bullshit) : CubicGaugePath :=
  { path with middleLeft := middleLeft }

def withMiddleRight
    (path : CubicGaugePath) (middleRight : Bullshit) : CubicGaugePath :=
  { path with middleRight := middleRight }

def leftMiddleResidual
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  (DiscreteGaugeDerivative.fromAction action).eulerLagrangeResidual
    path.leftFinitePath
    variation

def rightMiddleResidual
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  (DiscreteGaugeDerivative.fromAction action).eulerLagrangeResidual
    path.rightFinitePath
    variation

def leftCubicDifference
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  Int.ofNat (cubicCost action (path.withMiddleLeft variation.slip)) -
    Int.ofNat (cubicCost action path)

def rightCubicDifference
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  Int.ofNat (cubicCost action (path.withMiddleRight variation.slip)) -
    Int.ofNat (cubicCost action path)

theorem leftCubicDifference_eq_leftMiddleResidual
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : FiniteGaugeVariation) :
    leftCubicDifference action path variation =
      leftMiddleResidual action path variation := by
  unfold leftCubicDifference leftMiddleResidual cubicCost withMiddleLeft
    leftFinitePath DiscreteGaugeDerivative.eulerLagrangeResidual
    DiscreteGaugeDerivative.fromAction FiniteGaugeAction.leftVariation
    FiniteGaugeAction.rightVariation
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

theorem rightCubicDifference_eq_rightMiddleResidual
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : FiniteGaugeVariation) :
    rightCubicDifference action path variation =
      rightMiddleResidual action path variation := by
  unfold rightCubicDifference rightMiddleResidual cubicCost withMiddleRight
    rightFinitePath DiscreteGaugeDerivative.eulerLagrangeResidual
    DiscreteGaugeDerivative.fromAction FiniteGaugeAction.leftVariation
    FiniteGaugeAction.rightVariation
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

end CubicGaugePath

structure CubicGaugeVariation where
  middleLeftSlip : Bullshit
  middleRightSlip : Bullshit

namespace CubicGaugeVariation

def apply
    (variation : CubicGaugeVariation) (path : CubicGaugePath) :
    CubicGaugePath :=
  { path with
    middleLeft := variation.middleLeftSlip
    middleRight := variation.middleRightSlip }

def leftVariation
    (variation : CubicGaugeVariation) : FiniteGaugeVariation where
  slip := variation.middleLeftSlip

def rightVariation
    (variation : CubicGaugeVariation) : FiniteGaugeVariation where
  slip := variation.middleRightSlip

def coupledCubicDifference
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Int :=
  Int.ofNat (CubicGaugePath.cubicCost action (variation.apply path)) -
    Int.ofNat (CubicGaugePath.cubicCost action path)

def mixedCubicCoupling
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Int :=
  Int.ofNat
      (action.segmentCost variation.middleLeftSlip variation.middleRightSlip) -
    Int.ofNat
      (action.segmentCost variation.middleLeftSlip path.middleRight) -
    Int.ofNat
      (action.segmentCost path.middleLeft variation.middleRightSlip) +
    Int.ofNat
      (action.segmentCost path.middleLeft path.middleRight)

theorem coupledCubicDifference_eq_left_right_plus_mixed
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    coupledCubicDifference action path variation =
      CubicGaugePath.leftMiddleResidual
          action path (leftVariation variation) +
        CubicGaugePath.rightMiddleResidual
          action path (rightVariation variation) +
          mixedCubicCoupling action path variation := by
  unfold coupledCubicDifference mixedCubicCoupling CubicGaugeVariation.apply
    CubicGaugeVariation.leftVariation CubicGaugeVariation.rightVariation
    CubicGaugePath.leftMiddleResidual
    CubicGaugePath.rightMiddleResidual CubicGaugePath.cubicCost
    CubicGaugePath.leftFinitePath CubicGaugePath.rightFinitePath
    DiscreteGaugeDerivative.eulerLagrangeResidual
    DiscreteGaugeDerivative.fromAction FiniteGaugeAction.leftVariation
    FiniteGaugeAction.rightVariation
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

def mixedCouplingSolved
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Prop :=
  mixedCubicCoupling action path variation = 0

theorem coupledCubicDifference_eq_zero_of_middleResiduals_and_mixed
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation)
    (hLeft :
      CubicGaugePath.leftMiddleResidual
        action path (leftVariation variation) = 0)
    (hRight :
      CubicGaugePath.rightMiddleResidual
        action path (rightVariation variation) = 0)
    (hMixed : mixedCouplingSolved action path variation) :
    coupledCubicDifference action path variation = 0 := by
  have hMixedZero :
      mixedCubicCoupling action path variation = 0 :=
    hMixed
  rw [coupledCubicDifference_eq_left_right_plus_mixed,
    hLeft, hRight, hMixedZero]
  simp

structure CoupledCubicSolved
    (action : FiniteGaugeAction) (path : CubicGaugePath) where
  leftSolved :
    forall variation : FiniteGaugeVariation,
      CubicGaugePath.leftMiddleResidual
        action path variation = 0
  rightSolved :
    forall variation : FiniteGaugeVariation,
      CubicGaugePath.rightMiddleResidual
        action path variation = 0
  mixedSolved :
    forall variation : CubicGaugeVariation,
      mixedCouplingSolved action path variation

theorem coupledCubicDifference_eq_zero_of_coupledSolved
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    (solved : CoupledCubicSolved action path)
    (variation : CubicGaugeVariation) :
    coupledCubicDifference action path variation = 0 :=
  coupledCubicDifference_eq_zero_of_middleResiduals_and_mixed
    action
    path
    variation
    (solved.leftSolved (leftVariation variation))
    (solved.rightSolved (rightVariation variation))
    (solved.mixedSolved variation)

end CubicGaugeVariation

structure CubicMiddleNodeSupport
    (range : AdmissibleRange) (path : CubicGaugePath) where
  leftElephant : FiniteElephant
  rightElephant : FiniteElephant
  leftPartition : ElephantRealPartition range leftElephant
  rightPartition : ElephantRealPartition range rightElephant
  leftSupportsMiddleNode : leftElephant.body = path.middleLeft
  rightSupportsMiddleNode : rightElephant.body = path.middleRight

namespace CubicMiddleNodeSupport

def leftSupportedVariation
    {range : AdmissibleRange} {path : CubicGaugePath}
    (support : CubicMiddleNodeSupport range path)
    (variation : FiniteGaugeVariation) : Prop :=
  variation.slip ∈ support.leftElephant.candidates.entries

def rightSupportedVariation
    {range : AdmissibleRange} {path : CubicGaugePath}
    (support : CubicMiddleNodeSupport range path)
    (variation : FiniteGaugeVariation) : Prop :=
  variation.slip ∈ support.rightElephant.candidates.entries

def supportedEulerLagrange
    {range : AdmissibleRange} {path : CubicGaugePath}
    (support : CubicMiddleNodeSupport range path)
    (action : FiniteGaugeAction) : Prop :=
  (forall variation,
    support.leftSupportedVariation variation ->
      path.leftMiddleResidual action variation = 0) /\
  (forall variation,
    support.rightSupportedVariation variation ->
      path.rightMiddleResidual action variation = 0)

theorem left_partition_supports_middle_node
    {range : AdmissibleRange} {path : CubicGaugePath}
    (support : CubicMiddleNodeSupport range path) :
    support.leftElephant.body = path.middleLeft :=
  support.leftSupportsMiddleNode

theorem right_partition_supports_middle_node
    {range : AdmissibleRange} {path : CubicGaugePath}
    (support : CubicMiddleNodeSupport range path) :
    support.rightElephant.body = path.middleRight :=
  support.rightSupportsMiddleNode

end CubicMiddleNodeSupport

structure CubicPartitionedLanczosApproximation
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (range : AdmissibleRange) where
  support : CubicMiddleNodeSupport range path
  leftApproximation :
    PartitionedLanczosApproximation
      action
      path.leftFinitePath
      range
      support.leftElephant
  rightApproximation :
    PartitionedLanczosApproximation
      action
      path.rightFinitePath
      range
      support.rightElephant

namespace CubicPartitionedLanczosApproximation

theorem leftEulerLagrange
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : FiniteGaugeVariation)
    (h :
      approximation.support.leftSupportedVariation variation) :
    path.leftMiddleResidual action variation = 0 := by
  have hTerminal :
      approximation.leftApproximation.trace.terminalResidual variation = 0 :=
    approximation.leftApproximation.terminal_solved_on variation h
  have hMatches :
      approximation.leftApproximation.trace.terminalResidual variation =
        path.leftMiddleResidual action variation := by
    simpa [OrderedMultisetLanczosTrace.terminalResidual,
      cubicSplineResidual, CubicGaugePath.leftMiddleResidual] using
      approximation.leftApproximation.trace.terminal_matches_cubic variation
  exact Eq.trans (Eq.symm hMatches) hTerminal

theorem rightEulerLagrange
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : FiniteGaugeVariation)
    (h :
      approximation.support.rightSupportedVariation variation) :
    path.rightMiddleResidual action variation = 0 := by
  have hTerminal :
      approximation.rightApproximation.trace.terminalResidual variation = 0 :=
    approximation.rightApproximation.terminal_solved_on variation h
  have hMatches :
      approximation.rightApproximation.trace.terminalResidual variation =
        path.rightMiddleResidual action variation := by
    simpa [OrderedMultisetLanczosTrace.terminalResidual,
      cubicSplineResidual, CubicGaugePath.rightMiddleResidual] using
      approximation.rightApproximation.trace.terminal_matches_cubic variation
  exact Eq.trans (Eq.symm hMatches) hTerminal

theorem supportedEulerLagrange
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range) :
    approximation.support.supportedEulerLagrange action := by
  constructor
  · intro variation h
    exact approximation.leftEulerLagrange variation h
  · intro variation h
    exact approximation.rightEulerLagrange variation h

theorem partitions_derive_two_middle_equations
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range) :
    (forall variation,
      approximation.support.leftSupportedVariation variation ->
        path.leftMiddleResidual action variation = 0) /\
    (forall variation,
      approximation.support.rightSupportedVariation variation ->
        path.rightMiddleResidual action variation = 0) :=
  approximation.supportedEulerLagrange

theorem partitions_and_mixed_derive_coupledCubicDifference_zero
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : CubicGaugeVariation)
    (hLeft :
      approximation.support.leftSupportedVariation
        (CubicGaugeVariation.leftVariation variation))
    (hRight :
      approximation.support.rightSupportedVariation
        (CubicGaugeVariation.rightVariation variation))
    (hMixed :
      CubicGaugeVariation.mixedCouplingSolved action path variation) :
    CubicGaugeVariation.coupledCubicDifference
      action path variation = 0 :=
  CubicGaugeVariation.coupledCubicDifference_eq_zero_of_middleResiduals_and_mixed
    action
    path
    variation
    (approximation.leftEulerLagrange
      (CubicGaugeVariation.leftVariation variation)
      hLeft)
    (approximation.rightEulerLagrange
      (CubicGaugeVariation.rightVariation variation)
      hRight)
    hMixed

theorem supported_data_and_mixedCoupling_solve_coupledCubicVariation
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (variation : CubicGaugeVariation)
    (hLeft :
      approximation.support.leftSupportedVariation
        (CubicGaugeVariation.leftVariation variation))
    (hRight :
      approximation.support.rightSupportedVariation
        (CubicGaugeVariation.rightVariation variation))
    (hMixed :
      CubicGaugeVariation.mixedCouplingSolved action path variation) :
    CubicGaugeVariation.coupledCubicDifference
      action path variation = 0 :=
  CubicPartitionedLanczosApproximation.partitions_and_mixed_derive_coupledCubicDifference_zero
    approximation
    variation
    hLeft
    hRight
    hMixed

theorem partitions_and_mixed_derive_coupledSolved
    {action : FiniteGaugeAction} {path : CubicGaugePath}
    {range : AdmissibleRange}
    (approximation :
      CubicPartitionedLanczosApproximation action path range)
    (hLeft :
      forall variation : FiniteGaugeVariation,
        approximation.support.leftSupportedVariation variation)
    (hRight :
      forall variation : FiniteGaugeVariation,
        approximation.support.rightSupportedVariation variation)
    (hMixed :
      forall variation,
        CubicGaugeVariation.mixedCouplingSolved action path variation) :
    CubicGaugeVariation.CoupledCubicSolved action path := by
  refine
    { leftSolved := ?_
      rightSolved := ?_
      mixedSolved := hMixed }
  · intro variation
    exact
      approximation.leftEulerLagrange
        variation
        (hLeft variation)
  · intro variation
    exact
      approximation.rightEulerLagrange
        variation
        (hRight variation)

end CubicPartitionedLanczosApproximation

def truthCubicGaugePath : CubicGaugePath where
  source := .zero Fact.Truth
  middleLeft := .zero Fact.Truth
  middleRight := .zero Fact.Truth
  target := .zero Fact.Truth

def truthCubicMiddleNodeSupport :
    CubicMiddleNodeSupport truthAdmissibleRange truthCubicGaugePath where
  leftElephant := truthElephantSample
  rightElephant := truthElephantSample
  leftPartition := truthElephantRealPartition
  rightPartition := truthElephantRealPartition
  leftSupportsMiddleNode := rfl
  rightSupportsMiddleNode := rfl

def truthCubicPartitionedLanczosApproximation :
    CubicPartitionedLanczosApproximation
      truthTerminalAction
      truthCubicGaugePath
      truthAdmissibleRange where
  support := truthCubicMiddleNodeSupport
  leftApproximation := truthPartitionedLanczosApproximation
  rightApproximation := truthPartitionedLanczosApproximation

theorem truthCubicPartitionedEulerLagrange :
    truthCubicMiddleNodeSupport.supportedEulerLagrange
      truthTerminalAction := by
  constructor
  · intro variation h
    simp [CubicGaugePath.leftMiddleResidual,
      DiscreteGaugeDerivative.eulerLagrangeResidual,
      DiscreteGaugeDerivative.fromAction,
      FiniteGaugeAction.leftVariation,
      FiniteGaugeAction.rightVariation,
      truthTerminalAction,
      CubicGaugePath.leftFinitePath]
  · intro variation h
    simp [CubicGaugePath.rightMiddleResidual,
      DiscreteGaugeDerivative.eulerLagrangeResidual,
      DiscreteGaugeDerivative.fromAction,
      FiniteGaugeAction.leftVariation,
      FiniteGaugeAction.rightVariation,
      truthTerminalAction,
      CubicGaugePath.rightFinitePath]

theorem truthCubicPartitions_derive_two_middle_equations :
    (forall variation,
      truthCubicMiddleNodeSupport.leftSupportedVariation variation ->
        truthCubicGaugePath.leftMiddleResidual
          truthTerminalAction
          variation = 0) /\
    (forall variation,
      truthCubicMiddleNodeSupport.rightSupportedVariation variation ->
        truthCubicGaugePath.rightMiddleResidual
          truthTerminalAction
          variation = 0) :=
  by
    constructor
    · intro variation h
      simp [CubicGaugePath.leftMiddleResidual,
        DiscreteGaugeDerivative.eulerLagrangeResidual,
        DiscreteGaugeDerivative.fromAction,
        FiniteGaugeAction.leftVariation,
        FiniteGaugeAction.rightVariation,
        truthTerminalAction,
        CubicGaugePath.leftFinitePath]
    · intro variation h
      simp [CubicGaugePath.rightMiddleResidual,
        DiscreteGaugeDerivative.eulerLagrangeResidual,
        DiscreteGaugeDerivative.fromAction,
        FiniteGaugeAction.leftVariation,
        FiniteGaugeAction.rightVariation,
        truthTerminalAction,
        CubicGaugePath.rightFinitePath]

end Measurement
