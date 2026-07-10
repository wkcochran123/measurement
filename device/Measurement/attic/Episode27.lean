import Measurement.Episode26

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 27__: _The Squeezed Elephant_

Episode26 made the finite measurement profile explicit: load, transform, and
binary give a heartbeat selector on each finite support.

The remaining analytic move should not pretend that one finite spline already
is the continuum.  A B-spline basis gives a countable refinement tower.  Each
stage is finite.  The Weierstrass approximation theorem supplies the shrinking
upper bound.  The squeeze theorem is the small bridge that lets the finite
residual ride that bound to zero.

The point of this file is deliberately modest: it does not import a real
analysis library, and it does not prove Weierstrass.  It states the certificate
that Weierstrass/B-spline density supplies and proves the basis-independent
squeeze theorem used by both spline and FFT-style towers.

Flagship path:

* `DiscreteGaugeDerivative.fromAction_closedFlatAt_residue_eq_truth_zero`
* `law_of_spline_sufficiency`
* `OrderedMultisetLanczosTrace.terminal_residue_for_any_iteration_order`
* `CubicPartitionedLanczosApproximation.partitions_derive_two_middle_equations`
* `ThreeOperationMeasurement.fastestCandidate_unique`
* `PointwiseSqueezedResidual.residual_tends_zero`
* `CompletedWeierstrassFiniteElephantTower.limit_not_outside_completion`
* `CompletedResidualWeierstrassTower.residualTower_tends_zero_from_weierstrass_bound`
* `CompletedResidualWeierstrassTower.limit_in_completion_and_residual_squeezed_by_weierstrass`
* `CompletedResidualWeierstrassTower.limit_in_completion_and_terminalResidual_tends_zero`
-/

structure ApproximationScale where
  Magnitude : Type
  zero : Magnitude
  le : Magnitude -> Magnitude -> Prop
  tolerance : Magnitude -> Prop
  le_trans :
    forall {left middle right : Magnitude},
      le left middle -> le middle right -> le left right

namespace ApproximationScale

def TendsToZero
    (scale : ApproximationScale)
    (sequence : Nat -> scale.Magnitude) : Prop :=
  forall epsilon,
    scale.tolerance epsilon ->
      exists stage,
        forall n,
          stage <= n -> scale.le (sequence n) epsilon

theorem tendsToZero_mono
    {scale : ApproximationScale}
    {lower upper : Nat -> scale.Magnitude}
    (hUpper : scale.TendsToZero upper)
    (hLe : forall n, scale.le (lower n) (upper n)) :
    scale.TendsToZero lower := by
  intro epsilon hEpsilon
  rcases hUpper epsilon hEpsilon with ⟨stage, hStage⟩
  exact
    ⟨stage,
      fun n hn =>
        scale.le_trans
          (hLe n)
          (hStage n hn)⟩

end ApproximationScale

structure PointwiseSqueezedResidual
    (scale : ApproximationScale) (Test : Sort u) where
  residual : Nat -> Test -> scale.Magnitude
  bound : Nat -> Test -> scale.Magnitude
  zero_le_residual :
    forall n test,
      scale.le scale.zero (residual n test)
  residual_le_bound :
    forall n test,
      scale.le (residual n test) (bound n test)
  bound_tends_zero :
    forall test,
      scale.TendsToZero (fun n => bound n test)

namespace PointwiseSqueezedResidual

theorem residual_tends_zero
    {scale : ApproximationScale} {Test : Sort u}
    (squeeze : PointwiseSqueezedResidual scale Test)
    (test : Test) :
    scale.TendsToZero (fun n => squeeze.residual n test) :=
  ApproximationScale.tendsToZero_mono
    (squeeze.bound_tends_zero test)
    (fun n => squeeze.residual_le_bound n test)

theorem residual_squeezed_between_zero_and_bound
    {scale : ApproximationScale} {Test : Sort u}
    (squeeze : PointwiseSqueezedResidual scale Test)
    (n : Nat) (test : Test) :
    scale.le scale.zero (squeeze.residual n test) /\
      scale.le (squeeze.residual n test) (squeeze.bound n test) :=
  ⟨squeeze.zero_le_residual n test,
    squeeze.residual_le_bound n test⟩

end PointwiseSqueezedResidual

structure IntResidualMagnitude
    (scale : ApproximationScale) where
  ofInt : Int -> scale.Magnitude

structure ApproximateLanczosTrace
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  knots : SlipMultiset
  initial : LanczosState
  terminal : LanczosState
  iterates : LanczosIterates knots initial terminal
  terminal_matches_cubic :
    forall variation,
      terminal.residual variation = cubicSplineResidual action path variation
  terminal_solved_on :
    forall variation,
      variation.slip ∈ knots.entries ->
        terminal.residual variation = 0

namespace ApproximateLanczosTrace

def terminalResidual
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : ApproximateLanczosTrace action path)
    (variation : FiniteGaugeVariation) : Int :=
  trace.terminal.residual variation

def fromOrdered
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : OrderedMultisetLanczosTrace action path) :
    ApproximateLanczosTrace action path where
  knots := trace.knots
  initial := trace.initial
  terminal := trace.terminal
  iterates := trace.iterates
  terminal_matches_cubic := trace.terminal_matches_cubic
  terminal_solved_on := trace.terminal_solved_on

theorem terminalResidual_matches_cubic
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : ApproximateLanczosTrace action path)
    (variation : FiniteGaugeVariation) :
    trace.terminalResidual variation =
      cubicSplineResidual action path variation :=
  trace.terminal_matches_cubic variation

theorem terminalResidual_eq_zero_on
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (trace : ApproximateLanczosTrace action path)
    (variation : FiniteGaugeVariation)
    (h : variation.slip ∈ trace.knots.entries) :
    trace.terminalResidual variation = 0 :=
  trace.terminal_solved_on variation h

end ApproximateLanczosTrace

structure ResidualTowerRealizesLanczos
    (scale : ApproximationScale)
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  stageTrace : Nat -> ApproximateLanczosTrace action path
  magnitude : IntResidualMagnitude scale
  squeeze :
    PointwiseSqueezedResidual scale FiniteGaugeVariation
  residual_matches_terminal :
    forall n variation,
      squeeze.residual n variation =
        magnitude.ofInt ((stageTrace n).terminalResidual variation)

namespace ResidualTowerRealizesLanczos

theorem terminalResidualMagnitude_tends_zero
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (tower : ResidualTowerRealizesLanczos scale action path)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n =>
        tower.magnitude.ofInt
          ((tower.stageTrace n).terminalResidual variation)) := by
  intro epsilon hEpsilon
  rcases tower.squeeze.residual_tends_zero variation epsilon hEpsilon with
    ⟨stage, hStage⟩
  exact
    ⟨stage,
      fun n hn => by
        simpa [tower.residual_matches_terminal n variation] using
          hStage n hn⟩

theorem stage_terminalResidual_eq_zero_on
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (tower : ResidualTowerRealizesLanczos scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (h : variation.slip ∈ (tower.stageTrace n).knots.entries) :
    (tower.stageTrace n).terminalResidual variation = 0 :=
  (tower.stageTrace n).terminalResidual_eq_zero_on variation h

theorem residual_matches_terminal_on
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (tower : ResidualTowerRealizesLanczos scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (_h : variation.slip ∈ (tower.stageTrace n).knots.entries) :
    tower.squeeze.residual n variation =
      tower.magnitude.ofInt
        ((tower.stageTrace n).terminalResidual variation) :=
  tower.residual_matches_terminal n variation

end ResidualTowerRealizesLanczos

structure PolynomialWorkSchedule where
  work : Nat -> Nat
  polynomiallyBounded : Prop

inductive ApproximationBasis where
  | bspline
  | fft

structure BasisApproximationWitness
    (scale : ApproximationScale) where
  basis : ApproximationBasis
  squeeze :
    PointwiseSqueezedResidual scale FiniteGaugeVariation

namespace BasisApproximationWitness

theorem residual_tends_zero
    {scale : ApproximationScale}
    (witness : BasisApproximationWitness scale)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n => witness.squeeze.residual n variation) :=
  witness.squeeze.residual_tends_zero variation

end BasisApproximationWitness

structure BSplineWeierstrassWitness
    (scale : ApproximationScale) where
  squeeze :
    PointwiseSqueezedResidual scale FiniteGaugeVariation

namespace BSplineWeierstrassWitness

def toBasisWitness
    {scale : ApproximationScale}
    (witness : BSplineWeierstrassWitness scale) :
    BasisApproximationWitness scale where
  basis := .bspline
  squeeze := witness.squeeze

theorem residual_tends_zero
    {scale : ApproximationScale}
    (witness : BSplineWeierstrassWitness scale)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n => witness.squeeze.residual n variation) :=
  witness.toBasisWitness.residual_tends_zero variation

end BSplineWeierstrassWitness

structure FFTApproximationWitness
    (scale : ApproximationScale) where
  squeeze :
    PointwiseSqueezedResidual scale FiniteGaugeVariation

namespace FFTApproximationWitness

def toBasisWitness
    {scale : ApproximationScale}
    (witness : FFTApproximationWitness scale) :
    BasisApproximationWitness scale where
  basis := .fft
  squeeze := witness.squeeze

theorem residual_tends_zero
    {scale : ApproximationScale}
    (witness : FFTApproximationWitness scale)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n => witness.squeeze.residual n variation) :=
  witness.toBasisWitness.residual_tends_zero variation

end FFTApproximationWitness

structure FiniteElephantTower (range : AdmissibleRange) where
  stage : Nat -> FiniteElephant
  stage_inRange :
    forall n,
      (stage n).inRange range
  contains_refines :
    forall n slip,
      (slip = (stage n).body ∨
        slip ∈ (stage n).candidates.entries) ->
        slip = (stage (n + 1)).body ∨
          slip ∈ (stage (n + 1)).candidates.entries

namespace FiniteElephantTower

def Contains
    {range : AdmissibleRange}
    (tower : FiniteElephantTower range)
    (n : Nat) (slip : Bullshit) : Prop :=
  slip = (tower.stage n).body ∨
    slip ∈ (tower.stage n).candidates.entries

theorem contains_refines'
    {range : AdmissibleRange}
    (tower : FiniteElephantTower range)
    {n : Nat} {slip : Bullshit}
    (h : tower.Contains n slip) :
    tower.Contains (n + 1) slip :=
  tower.contains_refines n slip h

def InCompletion
    {range : AdmissibleRange}
    (tower : FiniteElephantTower range)
    (converges : (Nat -> Bullshit) -> Bullshit -> Prop)
    (limit : Bullshit) : Prop :=
  exists approximant : Nat -> Bullshit,
    (forall n, tower.Contains n (approximant n)) /\
      converges approximant limit

def OutsideCompletion
    {range : AdmissibleRange}
    (tower : FiniteElephantTower range)
    (converges : (Nat -> Bullshit) -> Bullshit -> Prop)
    (limit : Bullshit) : Prop :=
  ¬ tower.InCompletion converges limit

end FiniteElephantTower

structure WeierstrassFiniteElephantTower
    (range : AdmissibleRange)
    (scale : ApproximationScale) where
  tower : FiniteElephantTower range
  work : PolynomialWorkSchedule
  witness : BasisApproximationWitness scale

namespace WeierstrassFiniteElephantTower

theorem residual_tends_zero
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    (tower : WeierstrassFiniteElephantTower range scale)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n => tower.witness.squeeze.residual n variation) :=
  tower.witness.residual_tends_zero variation

def fromBSplineWitness
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    (tower : FiniteElephantTower range)
    (work : PolynomialWorkSchedule)
    (witness : BSplineWeierstrassWitness scale) :
    WeierstrassFiniteElephantTower range scale where
  tower := tower
  work := work
  witness := witness.toBasisWitness

def fromFFTWitness
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    (tower : FiniteElephantTower range)
    (work : PolynomialWorkSchedule)
    (witness : FFTApproximationWitness scale) :
    WeierstrassFiniteElephantTower range scale where
  tower := tower
  work := work
  witness := witness.toBasisWitness

end WeierstrassFiniteElephantTower

structure CompletedWeierstrassFiniteElephantTower
    (range : AdmissibleRange)
    (scale : ApproximationScale) where
  approximation :
    WeierstrassFiniteElephantTower range scale
  limit : Bullshit
  approximant : Nat -> Bullshit
  approximant_in_stage :
    forall n,
      approximation.tower.Contains n (approximant n)
  converges : (Nat -> Bullshit) -> Bullshit -> Prop
  converges_to_limit :
    converges approximant limit

namespace CompletedWeierstrassFiniteElephantTower

theorem limit_in_completion
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    (completed : CompletedWeierstrassFiniteElephantTower range scale) :
    completed.approximation.tower.InCompletion
      completed.converges
      completed.limit := by
  exact
    ⟨completed.approximant,
      completed.approximant_in_stage,
      completed.converges_to_limit⟩

theorem limit_not_outside_completion
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    (completed : CompletedWeierstrassFiniteElephantTower range scale) :
    ¬ completed.approximation.tower.OutsideCompletion
      completed.converges
      completed.limit := by
  intro hOutside
  exact hOutside completed.limit_in_completion

theorem residual_tends_zero
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    (completed : CompletedWeierstrassFiniteElephantTower range scale)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n =>
        completed.approximation.witness.squeeze.residual n variation) :=
  completed.approximation.residual_tends_zero variation

end CompletedWeierstrassFiniteElephantTower

structure CompletedResidualWeierstrassTower
    (range : AdmissibleRange)
    (scale : ApproximationScale)
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  completion :
    CompletedWeierstrassFiniteElephantTower range scale
  residualTower :
    ResidualTowerRealizesLanczos scale action path
  stage_matches_elephant :
    forall n,
      (residualTower.stageTrace n).knots =
        (completion.approximation.tower.stage n).candidates
  residualTower_le_weierstrass_bound :
    forall n variation,
      scale.le
        (residualTower.squeeze.residual n variation)
        (completion.approximation.witness.squeeze.bound n variation)

namespace CompletedResidualWeierstrassTower

theorem limit_not_outside_completion
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed :
      CompletedResidualWeierstrassTower range scale action path) :
    ¬ completed.completion.approximation.tower.OutsideCompletion
      completed.completion.converges
      completed.completion.limit :=
  CompletedWeierstrassFiniteElephantTower.limit_not_outside_completion
    completed.completion

theorem residualTower_tends_zero_from_weierstrass_bound
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed :
      CompletedResidualWeierstrassTower range scale action path)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n =>
        completed.residualTower.squeeze.residual n variation) :=
  ApproximationScale.tendsToZero_mono
    (completed.completion.approximation.witness.squeeze.bound_tends_zero
      variation)
    (fun n =>
      completed.residualTower_le_weierstrass_bound n variation)

theorem terminalResidualMagnitude_tends_zero
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed :
      CompletedResidualWeierstrassTower range scale action path)
    (variation : FiniteGaugeVariation) :
    scale.TendsToZero
      (fun n =>
        completed.residualTower.magnitude.ofInt
          ((completed.residualTower.stageTrace n).terminalResidual
            variation)) := by
  intro epsilon hEpsilon
  rcases
    completed.residualTower_tends_zero_from_weierstrass_bound
      variation
      epsilon
      hEpsilon with
    ⟨stage, hStage⟩
  exact
    ⟨stage,
      fun n hn => by
        simpa [completed.residualTower.residual_matches_terminal n variation] using
          hStage n hn⟩

theorem stage_knots_match_elephant
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed :
      CompletedResidualWeierstrassTower range scale action path)
    (n : Nat) :
    (completed.residualTower.stageTrace n).knots =
      (completed.completion.approximation.tower.stage n).candidates :=
  completed.stage_matches_elephant n

theorem stageTrace_solves_elephant_support
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed :
      CompletedResidualWeierstrassTower range scale action path)
    (n : Nat)
    (variation : FiniteGaugeVariation)
    (h :
      variation.slip ∈
        (completed.completion.approximation.tower.stage n).candidates.entries) :
    (completed.residualTower.stageTrace n).terminalResidual variation = 0 :=
  completed.residualTower.stage_terminalResidual_eq_zero_on
    n
    variation
    (by
      simpa [completed.stage_matches_elephant n] using h)

theorem limit_in_completion_and_residual_squeezed_by_weierstrass
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed :
      CompletedResidualWeierstrassTower range scale action path)
    (variation : FiniteGaugeVariation) :
    (¬ completed.completion.approximation.tower.OutsideCompletion
      completed.completion.converges
      completed.completion.limit) /\
    scale.TendsToZero
      (fun n =>
        completed.residualTower.squeeze.residual n variation) :=
  ⟨CompletedResidualWeierstrassTower.limit_not_outside_completion completed,
    CompletedResidualWeierstrassTower.residualTower_tends_zero_from_weierstrass_bound
      completed
      variation⟩

theorem limit_in_completion_and_terminalResidual_tends_zero
    {range : AdmissibleRange}
    {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed :
      CompletedResidualWeierstrassTower range scale action path)
    (variation : FiniteGaugeVariation) :
    (¬ completed.completion.approximation.tower.OutsideCompletion
      completed.completion.converges
      completed.completion.limit) /\
    scale.TendsToZero
      (fun n =>
        completed.residualTower.magnitude.ofInt
          ((completed.residualTower.stageTrace n).terminalResidual
            variation)) :=
  ⟨CompletedResidualWeierstrassTower.limit_not_outside_completion completed,
    CompletedResidualWeierstrassTower.terminalResidualMagnitude_tends_zero
      completed
      variation⟩

end CompletedResidualWeierstrassTower

def truthApproximationScale : ApproximationScale where
  Magnitude := Unit
  zero := ()
  le := fun _ _ => True
  tolerance := fun _ => True
  le_trans := by
    intro left middle right hLeft hRight
    trivial

def truthSqueezedResidual :
    PointwiseSqueezedResidual
      truthApproximationScale
      FiniteGaugeVariation where
  residual := fun _ _ => ()
  bound := fun _ _ => ()
  zero_le_residual := by
    intro n test
    trivial
  residual_le_bound := by
    intro n test
    trivial
  bound_tends_zero := by
    intro test epsilon hEpsilon
    exact ⟨0, by intro n hn; trivial⟩

def truthBSplineWeierstrassWitness :
    BSplineWeierstrassWitness truthApproximationScale where
  squeeze := truthSqueezedResidual

def truthApproximateLanczosTrace :
    ApproximateLanczosTrace truthTerminalAction truthTerminalPath :=
  ApproximateLanczosTrace.fromOrdered truthTerminalTrace

def truthIntResidualMagnitude :
    IntResidualMagnitude truthApproximationScale where
  ofInt := fun _ => ()

def truthResidualTowerRealizesLanczos :
    ResidualTowerRealizesLanczos
      truthApproximationScale
      truthTerminalAction
      truthTerminalPath where
  stageTrace := fun _ => truthApproximateLanczosTrace
  magnitude := truthIntResidualMagnitude
  squeeze := truthSqueezedResidual
  residual_matches_terminal := by
    intro n variation
    rfl

def truthPolynomialWorkSchedule : PolynomialWorkSchedule where
  work := fun _ => 0
  polynomiallyBounded := True

def truthFiniteElephantTower :
    FiniteElephantTower truthAdmissibleRange where
  stage := fun _ => truthElephantSample
  stage_inRange := by
    intro n
    exact truthElephantSample_inRange
  contains_refines := by
    intro n slip h
    exact h

def truthWeierstrassFiniteElephantTower :
    WeierstrassFiniteElephantTower
      truthAdmissibleRange
      truthApproximationScale :=
  WeierstrassFiniteElephantTower.fromBSplineWitness
    truthFiniteElephantTower
    truthPolynomialWorkSchedule
    truthBSplineWeierstrassWitness

def truthCompletedWeierstrassFiniteElephantTower :
    CompletedWeierstrassFiniteElephantTower
      truthAdmissibleRange
      truthApproximationScale where
  approximation := truthWeierstrassFiniteElephantTower
  limit := .zero Fact.Truth
  approximant := fun _ => .zero Fact.Truth
  approximant_in_stage := by
    intro n
    left
    rfl
  converges := fun approximant limit =>
    forall n, approximant n = limit
  converges_to_limit := by
    intro n
    rfl

theorem truthCompletedWeierstrass_residual_tends_zero
    (variation : FiniteGaugeVariation) :
    truthApproximationScale.TendsToZero
      (fun n =>
        truthCompletedWeierstrassFiniteElephantTower.approximation.witness.squeeze.residual
          n
          variation) :=
  by
    intro epsilon hEpsilon
    exact ⟨0, by intro n hn; trivial⟩

theorem truthCompletedWeierstrass_limit_not_outside :
    ¬ truthCompletedWeierstrassFiniteElephantTower.approximation.tower.OutsideCompletion
      truthCompletedWeierstrassFiniteElephantTower.converges
      truthCompletedWeierstrassFiniteElephantTower.limit :=
  truthCompletedWeierstrassFiniteElephantTower.limit_not_outside_completion

def truthCompletedResidualWeierstrassTower :
    CompletedResidualWeierstrassTower
      truthAdmissibleRange
      truthApproximationScale
      truthTerminalAction
      truthTerminalPath where
  completion := truthCompletedWeierstrassFiniteElephantTower
  residualTower := truthResidualTowerRealizesLanczos
  stage_matches_elephant := by
    intro n
    rfl
  residualTower_le_weierstrass_bound := by
    intro n variation
    trivial

theorem truthCompletedResidualWeierstrass_pipeline
    (variation : FiniteGaugeVariation) :
    (¬ truthCompletedResidualWeierstrassTower.completion.approximation.tower.OutsideCompletion
      truthCompletedResidualWeierstrassTower.completion.converges
      truthCompletedResidualWeierstrassTower.completion.limit) /\
    truthApproximationScale.TendsToZero
      (fun n =>
        truthCompletedResidualWeierstrassTower.residualTower.magnitude.ofInt
          ((truthCompletedResidualWeierstrassTower.residualTower.stageTrace n).terminalResidual
            variation)) :=
  by
    constructor
    · intro hOutside
      exact
        hOutside
          truthCompletedResidualWeierstrassTower.completion.limit_in_completion
    · intro epsilon hEpsilon
      exact ⟨0, by intro n hn; trivial⟩

end Measurement
