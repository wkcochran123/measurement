import Measurement.Episode21

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 22__: _Real Partitions_

Episode21 finished the finite Lanczos law: a completed multiset iterator
collapses to the cubic-spline certificate and hence to residue
`.zero Fact.Truth`.

The analytic lift needs one more bridge before Sobolev language is honest.
Each finite elephant in the admissible range must be assigned a real
partition.  This file introduces that contract without importing an analytic
library: the "real line" is an abstract ordered coordinate system with a
mesh.  Later episodes can instantiate it with actual real/Sobolev structure.

Stated formally:
supported candidate variations transfer through `knots_match` to trace-knot
residuals.

Claimed by interpretation:
the spline represents the finite data on those knots.

Residue left:
continuum/global variation control is deferred to the squeezed tower.
-/

structure RealCoordinateSystem where
  Point : Type
  le : Point -> Point -> Prop
  distance : Point -> Point -> Nat

structure RealPartition where
  axis : RealCoordinateSystem
  cellCount : Nat
  mesh : Nat
  point : Nat -> axis.Point
  ordered :
    forall index,
      axis.le (point index) (point (index + 1))
  boundedStep :
    forall index,
      axis.distance (point index) (point (index + 1)) <= mesh

structure AdmissibleRange where
  contains : Bullshit -> Prop

structure FiniteElephant where
  body : Bullshit
  candidates : SlipMultiset

namespace FiniteElephant

def inRange (elephant : FiniteElephant) (range : AdmissibleRange) : Prop :=
  range.contains elephant.body /\
    forall slip,
      slip ∈ elephant.candidates.entries ->
        range.contains slip

end FiniteElephant

structure ElephantRealPartition
    (range : AdmissibleRange) (elephant : FiniteElephant) where
  partition : RealPartition
  covers : elephant.inRange range
  locate : Bullshit -> partition.axis.Point
  locates_candidates :
    forall slip,
      slip ∈ elephant.candidates.entries ->
        range.contains slip

structure RealPartitionConstructor (range : AdmissibleRange) where
  construct :
    (elephant : FiniteElephant) ->
      elephant.inRange range ->
        ElephantRealPartition range elephant

namespace RealPartitionConstructor

def partition
    {range : AdmissibleRange}
    (constructor : RealPartitionConstructor range)
    (elephant : FiniteElephant)
    (h : elephant.inRange range) :
    RealPartition :=
  (constructor.construct elephant h).partition

end RealPartitionConstructor

structure PartitionSobolevSpace (partition : RealPartition) where
  Function : Type
  weakPairing : Function -> Function -> Int
  generatedBy : SlipMultiset -> Function

structure PartitionedLanczosApproximation
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (range : AdmissibleRange) (elephant : FiniteElephant) where
  trace : OrderedMultisetLanczosTrace action path
  partitioned : ElephantRealPartition range elephant
  sobolevSpace : PartitionSobolevSpace partitioned.partition
  -- The finite elephant supplies the data support.  The Lanczos trace supplies
  -- the spline knots.  `knots_match` identifies these supports, so solving the
  -- trace residual on its knots solves the spline/data residual on the elephant.
  knots_match : trace.knots = elephant.candidates

namespace PartitionedLanczosApproximation

def weakResidual
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (test : FiniteGaugeVariation) : Int :=
  approximation.trace.terminalResidual test

theorem weakResidual_eq_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (test : FiniteGaugeVariation) :
    approximation.weakResidual test = 0 :=
  approximation.trace.terminalResidual_eq_zero test

theorem terminal_solved_on
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (test : FiniteGaugeVariation)
    (h : test.slip ∈ elephant.candidates.entries) :
    approximation.trace.terminalResidual test = 0 :=
  approximation.trace.terminalResidual_eq_zero_on test
    (by
      simpa [approximation.knots_match] using h)

theorem weakResidual_eq_zero_on
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (test : FiniteGaugeVariation)
    (h : test.slip ∈ elephant.candidates.entries) :
    approximation.weakResidual test = 0 :=
  approximation.terminal_solved_on test h

theorem trace_knots_sameSupport_elephant
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant) :
    approximation.trace.knots.sameSupport elephant.candidates :=
  SlipMultiset.sameSupport_of_eq approximation.knots_match

theorem spline_represents_supported_data
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (test : FiniteGaugeVariation)
    (h : test.slip ∈ elephant.candidates.entries) :
    approximation.trace.terminalResidual test = 0 :=
  approximation.terminal_solved_on test h

theorem spline_represents_cubic_residual_on_supported_data
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant)
    (test : FiniteGaugeVariation)
    (h : test.slip ∈ elephant.candidates.entries) :
    cubicSplineResidual action path test = 0 := by
  exact Eq.trans
    (Eq.symm (approximation.trace.terminalResidual_matches_cubic test))
    (approximation.terminal_solved_on test h)

theorem cubicSplineBalancedOn_supported_data
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant) :
    cubicSplineBalancedOn elephant.candidates action path :=
  ⟨approximation.trace.admits,
    by
      intro variation h
      exact
        approximation.spline_represents_cubic_residual_on_supported_data
          variation
          h⟩

theorem eulerLagrange
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant) :
    (DiscreteGaugeDerivative.fromAction action).eulerLagrange path :=
  approximation.trace.eulerLagrange

theorem residue_eq_truth_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    {range : AdmissibleRange} {elephant : FiniteElephant}
    (approximation :
      PartitionedLanczosApproximation action path range elephant) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  approximation.trace.residue_eq_truth_zero

end PartitionedLanczosApproximation

def trivialRealAxis : RealCoordinateSystem where
  Point := Unit
  le := fun _ _ => True
  distance := fun _ _ => 0

def trivialRealPartition : RealPartition where
  axis := trivialRealAxis
  cellCount := 1
  mesh := 0
  point := fun _ => ()
  ordered := by
    intro index
    trivial
  boundedStep := by
    intro index
    exact Nat.le_refl _

def truthAdmissibleRange : AdmissibleRange where
  contains := fun _ => True

def truthElephantSample : FiniteElephant where
  body := .zero Fact.Truth
  candidates := SlipMultiset.singleton (.zero Fact.Truth)

theorem truthElephantSample_inRange :
    truthElephantSample.inRange truthAdmissibleRange := by
  constructor
  · trivial
  · intro slip h
    trivial

def truthElephantRealPartition :
    ElephantRealPartition truthAdmissibleRange truthElephantSample where
  partition := trivialRealPartition
  covers := truthElephantSample_inRange
  locate := fun _ => ()
  locates_candidates := by
    intro slip h
    trivial

def truthPartitionSobolevSpace :
    PartitionSobolevSpace truthElephantRealPartition.partition where
  Function := Unit
  weakPairing := fun _ _ => 0
  generatedBy := fun _ => ()

def truthPartitionedLanczosApproximation :
    PartitionedLanczosApproximation
      truthTerminalAction
      truthTerminalPath
      truthAdmissibleRange
      truthElephantSample where
  trace := truthTerminalTrace
  partitioned := truthElephantRealPartition
  sobolevSpace := truthPartitionSobolevSpace
  knots_match := rfl

theorem truthPartitionedLanczos_weakResidual_eq_zero
    (test : FiniteGaugeVariation) :
    truthPartitionedLanczosApproximation.weakResidual test = 0 :=
  truthPartitionedLanczosApproximation.weakResidual_eq_zero test

theorem truthPartitionedLanczos_residue_eq_truth_zero :
    (DiscreteGaugeDerivative.fromAction truthTerminalAction).residue
      truthTerminalPath = .zero Fact.Truth :=
  truthTerminalTrace_residue_eq_truth_zero

end Measurement
