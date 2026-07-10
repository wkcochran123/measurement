import Measurement.Episode22

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 23__: _Partitioned Functions_

Episode22 introduced the real-partition contract for each finite elephant
in the admissible range.  This episode packages the first honest analytic
object over that contract: an abstract `R -> R` function.

There is still no imported real-analysis library here.  The "real" line is
the coordinate system supplied by the partition.  The important bridge is
that the finite proof mechanism now realizes a partitioned function whose
weak residual is exactly the residual discharged by the Lanczos trace.
-/

structure AnalyticFunction (axis : RealCoordinateSystem) where
  map : axis.Point -> axis.Point

namespace AnalyticFunction

def identity (axis : RealCoordinateSystem) : AnalyticFunction axis where
  map := fun point => point

def compose
    {axis : RealCoordinateSystem}
    (g f : AnalyticFunction axis) : AnalyticFunction axis where
  map := fun point => g.map (f.map point)

end AnalyticFunction

structure PartitionedFunction (partition : RealPartition) where
  function : AnalyticFunction partition.axis
  sampled : Nat -> partition.axis.Point
  sampled_eq :
    forall index,
      sampled index = function.map (partition.point index)

namespace PartitionedFunction

def fromAnalytic
    (partition : RealPartition)
    (function : AnalyticFunction partition.axis) :
    PartitionedFunction partition where
  function := function
  sampled := fun index => function.map (partition.point index)
  sampled_eq := by
    intro index
    rfl

def identity (partition : RealPartition) :
    PartitionedFunction partition :=
  fromAnalytic partition (AnalyticFunction.identity partition.axis)

end PartitionedFunction

structure PartitionedSplineFunction
    (partition : RealPartition) extends PartitionedFunction partition where
  cubicResidual : Nat -> Int
  weakResidual : FiniteGaugeVariation -> Int
  residual_zero :
    forall test,
      weakResidual test = 0

namespace PartitionedSplineFunction

def fromApproximation
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (function : PartitionedFunction approximation.partitioned.partition) :
    PartitionedSplineFunction approximation.partitioned.partition where
  function := function.function
  sampled := function.sampled
  sampled_eq := function.sampled_eq
  cubicResidual := fun _ => 0
  weakResidual := approximation.weakResidual
  residual_zero := by
    intro test
    exact approximation.weakResidual_eq_zero test

end PartitionedSplineFunction

structure RealizedPartitionedLanczosApproximation
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (range : AdmissibleRange) (elephant : FiniteElephant) where
  approximation :
    PartitionedLanczosApproximation action path range elephant
  function :
    PartitionedSplineFunction approximation.partitioned.partition
  residual_matches_trace :
    forall test,
      function.weakResidual test = approximation.weakResidual test

namespace RealizedPartitionedLanczosApproximation

theorem weakResidual_eq_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (realization :
      RealizedPartitionedLanczosApproximation action path range elephant)
    (test : FiniteGaugeVariation) :
    realization.function.weakResidual test = 0 := by
  rw [realization.residual_matches_trace test]
  exact realization.approximation.weakResidual_eq_zero test

theorem residue_eq_truth_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (realization :
      RealizedPartitionedLanczosApproximation action path range elephant) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  realization.approximation.residue_eq_truth_zero

theorem eulerLagrange
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (realization :
      RealizedPartitionedLanczosApproximation action path range elephant) :
    (DiscreteGaugeDerivative.fromAction action).eulerLagrange path :=
  realization.approximation.eulerLagrange

end RealizedPartitionedLanczosApproximation

def realizeFromPartitionedFunction
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (function : PartitionedFunction approximation.partitioned.partition) :
    RealizedPartitionedLanczosApproximation action path range elephant where
  approximation := approximation
  function :=
    PartitionedSplineFunction.fromApproximation approximation function
  residual_matches_trace := by
    intro test
    rfl

def truthPartitionedFunction :
    PartitionedFunction trivialRealPartition :=
  PartitionedFunction.identity trivialRealPartition

def truthPartitionedSplineFunction :
    PartitionedSplineFunction trivialRealPartition where
  function := AnalyticFunction.identity trivialRealPartition.axis
  sampled := fun _ => ()
  sampled_eq := by
    intro index
    rfl
  cubicResidual := fun _ => 0
  weakResidual := fun _ => 0
  residual_zero := by
    intro test
    rfl

def truthRealizedPartitionedLanczosApproximation :
    RealizedPartitionedLanczosApproximation
      truthTerminalAction
      truthTerminalPath
      truthAdmissibleRange
      truthElephantSample where
  approximation := truthPartitionedLanczosApproximation
  function := truthPartitionedSplineFunction
  residual_matches_trace := by
    intro test
    rw [truthPartitionedSplineFunction.residual_zero test]
    exact Eq.symm
      (truthPartitionedLanczosApproximation.weakResidual_eq_zero test)

theorem truthRealizedPartitionedFunction_weakResidual_eq_zero
    (test : FiniteGaugeVariation) :
    truthRealizedPartitionedLanczosApproximation.function.weakResidual test =
      0 := by
  rfl

theorem truthRealizedPartitionedFunction_residue_eq_truth_zero :
    (DiscreteGaugeDerivative.fromAction truthTerminalAction).residue
      truthTerminalPath = .zero Fact.Truth :=
  truthPartitionedLanczos_residue_eq_truth_zero

end Measurement
