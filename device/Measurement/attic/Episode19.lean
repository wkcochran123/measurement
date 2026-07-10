import Measurement.Episode18

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 19__: _Euler-Lagrange_

Episode18 gave the first variation.  Euler-Lagrange is what remains when
that variation is split into the left and right contributions at the
middle point and stationarity forces their sum to vanish.

Stated formally:
`totalResidualVanished` is the two-channel detector.  The direct/composed
residual must vanish, and the Euler-Lagrange residual must vanish for every
finite variation.

Claimed by interpretation:
when a path is closed-flat, the slip coordinate is pure gauge, so both
detectors go quiet.

Residue left:
none for the finite theorem; analytic convergence is handled later by the
squeezed finite-elephant tower.
-/

structure DiscreteGaugeDerivative where
  gauge : FrechetGauge
  leftDerivative : FiniteGaugePath -> FiniteGaugeVariation -> Int
  rightDerivative : FiniteGaugePath -> FiniteGaugeVariation -> Int
  decomposition :
    forall path variation,
      gauge.linearPart path variation =
        leftDerivative path variation + rightDerivative path variation

namespace DiscreteGaugeDerivative

def eulerLagrange
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) : Prop :=
  forall variation,
    derivative.leftDerivative path variation +
      derivative.rightDerivative path variation = 0

def eulerLagrangeResidual
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  derivative.leftDerivative path variation +
    derivative.rightDerivative path variation

def residualVanished
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) : Prop :=
  forall variation,
    derivative.eulerLagrangeResidual path variation = 0

def directResidual
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) : Int :=
  Int.ofNat (derivative.gauge.action.direct path) -
    Int.ofNat (derivative.gauge.action.composed path)

def totalResidual
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  derivative.directResidual path +
    derivative.eulerLagrangeResidual path variation

def totalResidualVanished
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) : Prop :=
  derivative.directResidual path = 0 /\
    derivative.residualVanished path

theorem residualVanished_iff_eulerLagrange
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) :
    derivative.residualVanished path <-> derivative.eulerLagrange path :=
  Iff.rfl

theorem totalResidual_eq_zero_of_totalResidualVanished
    (derivative : DiscreteGaugeDerivative) {path : FiniteGaugePath}
    (h : derivative.totalResidualVanished path)
    (variation : FiniteGaugeVariation) :
    derivative.totalResidual path variation = 0 := by
  unfold totalResidual
  rw [h.left, h.right variation]
  simp

theorem totalResidualVanished_iff_directResidual_eq_zero_and_eulerLagrange
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) :
    derivative.totalResidualVanished path <->
      derivative.directResidual path = 0 /\
        derivative.eulerLagrange path := by
  constructor
  · intro h
    exact
      ⟨h.left,
        (derivative.residualVanished_iff_eulerLagrange path).1 h.right⟩
  · intro h
    exact
      ⟨h.left,
        (derivative.residualVanished_iff_eulerLagrange path).2 h.right⟩

/-- The oracle is the Euler-Lagrange equation.  Stationarity -- whether the
first variation vanishes for EVERY variation -- is a universal over the infinite
variation space, not a computation.  The construction computes the direct
residual; it must consult an oracle for stationarity.  This is the axiom of
choice in its physical form: the law of motion is the one query nature answers
that the machine cannot. -/
axiom eulerLagrangeOracle
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) :
    Decidable (derivative.eulerLagrange path)

noncomputable def residue
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) : Bullshit :=
  haveI : Decidable (derivative.residualVanished path) :=
    eulerLagrangeOracle derivative path
  haveI : Decidable (derivative.totalResidualVanished path) :=
    inferInstanceAs
      (Decidable (derivative.directResidual path = 0 ∧ derivative.residualVanished path))
  if derivative.totalResidualVanished path then
    .zero Fact.Truth
  else
    path.target

theorem totalResidualVanished_residue_eq_truth_zero
    (derivative : DiscreteGaugeDerivative) {path : FiniteGaugePath}
    (h : derivative.totalResidualVanished path) :
    derivative.residue path = .zero Fact.Truth := by
  simp [residue, h]

def fromAction (action : FiniteGaugeAction) : DiscreteGaugeDerivative where
  gauge := FrechetGauge.fromAction action
  leftDerivative := action.leftVariation
  rightDerivative := action.rightVariation
  decomposition := by
    intro path variation
    rfl

theorem fromAction_directResidual_eq_zero_of_admits
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.admits path) :
    (fromAction action).directResidual path = 0 := by
  unfold directResidual fromAction
  change
    Int.ofNat (action.direct path) -
      Int.ofNat (action.composed path) = 0
  rw [h]
  simp

theorem stationary_implies_eulerLagrange
    (derivative : DiscreteGaugeDerivative) {path : FiniteGaugePath}
    (h : derivative.gauge.stationaryAt path) :
    derivative.eulerLagrange path := by
  intro variation
  exact Eq.trans
    (Eq.symm (derivative.decomposition path variation))
    (h variation)

theorem eulerLagrange_implies_stationary
    (derivative : DiscreteGaugeDerivative) {path : FiniteGaugePath}
    (h : derivative.eulerLagrange path) :
    derivative.gauge.stationaryAt path := by
  intro variation
  exact Eq.trans
    (derivative.decomposition path variation)
    (h variation)

theorem stationary_iff_eulerLagrange
    (derivative : DiscreteGaugeDerivative) (path : FiniteGaugePath) :
    derivative.gauge.stationaryAt path <-> derivative.eulerLagrange path :=
  ⟨derivative.stationary_implies_eulerLagrange,
    derivative.eulerLagrange_implies_stationary⟩

theorem fromAction_closedFlatAt_totalResidualVanished
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    (fromAction action).totalResidualVanished path := by
  constructor
  · exact fromAction_directResidual_eq_zero_of_admits h.left
  · intro variation
    have hs :
        (fromAction action).gauge.stationaryAt path :=
      FrechetGauge.fromAction_stationaryAt_of_flatAt h.right
    have hel :
        (fromAction action).eulerLagrange path :=
      (fromAction action).stationary_implies_eulerLagrange hs
    exact hel variation

theorem eulerLagrange_residue_eq_truth_zero
    (derivative : DiscreteGaugeDerivative) {path : FiniteGaugePath}
    (hDirect : derivative.directResidual path = 0)
    (h : derivative.eulerLagrange path) :
    derivative.residue path = .zero Fact.Truth := by
  have hv : derivative.residualVanished path :=
    (derivative.residualVanished_iff_eulerLagrange path).2 h
  have ht : derivative.totalResidualVanished path :=
    ⟨hDirect, hv⟩
  exact derivative.totalResidualVanished_residue_eq_truth_zero ht

theorem stationary_residue_eq_truth_zero
    (derivative : DiscreteGaugeDerivative) {path : FiniteGaugePath}
    (hDirect : derivative.directResidual path = 0)
    (h : derivative.gauge.stationaryAt path) :
    derivative.residue path = .zero Fact.Truth :=
  derivative.eulerLagrange_residue_eq_truth_zero
    hDirect
    (derivative.stationary_implies_eulerLagrange h)

theorem fromAction_closedFlatAt_residue_eq_truth_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    (fromAction action).residue path = .zero Fact.Truth :=
  (fromAction action).totalResidualVanished_residue_eq_truth_zero
    (fromAction_closedFlatAt_totalResidualVanished h)

end DiscreteGaugeDerivative

end Measurement
