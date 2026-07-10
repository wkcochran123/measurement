import Measurement.Episode19

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 20__: _Spline Sufficiency_

Episode19 recovered the discrete Euler-Lagrange balance from stationarity
and closed the residue at `.zero Fact.Truth`.

This episode names the missing solver layer.  A Lanczos certificate is not
an image-processing kernel here; it is the finite tridiagonal generator whose
residual is the same residual as the cubic/Frechet gauge.  Once that residual
is solved, the cubic spline closure and the Lanczos closure are the same
finite object.

Stated formally:
`cubicSplineBalanced` means direct/composed closure plus a zero cubic/Frechet
residual. `cubicSplineClosed` is the stronger closed-flat way to produce that
balance.

Claimed by interpretation:
a solved Lanczos tridiagonal residual is enough because it is identified with
the cubic spline residual, which is identified with the gauge residual.

Residue left:
the solver trace is still a certificate consumer.  It proves collapse from a
completed trace; it does not yet prove arbitrary Lanczos convergence.
-/

def cubicSplineResidual
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  (DiscreteGaugeDerivative.fromAction action).eulerLagrangeResidual
    path
    variation

def cubicSplineClosed
    (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.closedFlatAt path /\
    forall variation,
      cubicSplineResidual action path variation = 0

def cubicSplineBalanced
    (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.admits path /\
    forall variation,
      cubicSplineResidual action path variation = 0

theorem cubicSplineClosed_balanced
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : cubicSplineClosed action path) :
    cubicSplineBalanced action path :=
  ⟨h.left.left, h.right⟩

theorem cubicSplineBalanced_totalResidualVanished
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : cubicSplineBalanced action path) :
    (DiscreteGaugeDerivative.fromAction action).totalResidualVanished path := by
  constructor
  · exact
      DiscreteGaugeDerivative.fromAction_directResidual_eq_zero_of_admits
        h.left
  · intro variation
    simpa [cubicSplineResidual] using h.right variation

theorem cubicSplineBalanced_residue_eq_truth_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : cubicSplineBalanced action path) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  (DiscreteGaugeDerivative.fromAction action).totalResidualVanished_residue_eq_truth_zero
    (cubicSplineBalanced_totalResidualVanished h)

theorem cubicSplineClosed_totalResidualVanished
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : cubicSplineClosed action path) :
    (DiscreteGaugeDerivative.fromAction action).totalResidualVanished path :=
  cubicSplineBalanced_totalResidualVanished
    (cubicSplineClosed_balanced h)

theorem cubicSplineClosed_residue_eq_truth_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : cubicSplineClosed action path) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  cubicSplineBalanced_residue_eq_truth_zero
    (cubicSplineClosed_balanced h)

structure LanczosCubicSpline
    (action : FiniteGaugeAction) (path : FiniteGaugePath) where
  tridiagonalResidual : FiniteGaugeVariation -> Int
  splineResidual : FiniteGaugeVariation -> Int
  sameResidual :
    forall variation,
      tridiagonalResidual variation = splineResidual variation
  solved :
    forall variation,
      tridiagonalResidual variation = 0
  matchesGauge :
    forall variation,
      splineResidual variation = cubicSplineResidual action path variation
  admits : action.admits path

namespace LanczosCubicSpline

theorem residual_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    forall variation,
      cubicSplineResidual action path variation = 0 := by
  intro variation
  rw [← certificate.matchesGauge variation]
  rw [← certificate.sameResidual variation]
  exact certificate.solved variation

theorem lanczos_equals_cubic_residual
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path)
    (variation : FiniteGaugeVariation) :
    certificate.tridiagonalResidual variation =
      cubicSplineResidual action path variation := by
  rw [certificate.sameResidual variation]
  exact certificate.matchesGauge variation

theorem cubic_balanced
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    cubicSplineBalanced action path :=
  ⟨certificate.admits, certificate.residual_zero⟩

theorem totalResidualVanished
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    (DiscreteGaugeDerivative.fromAction action).totalResidualVanished path :=
  cubicSplineBalanced_totalResidualVanished certificate.cubic_balanced

theorem eulerLagrange
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    (DiscreteGaugeDerivative.fromAction action).eulerLagrange path := by
  intro variation
  exact certificate.residual_zero variation

theorem stationary
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    (DiscreteGaugeDerivative.fromAction action).gauge.stationaryAt path :=
  (DiscreteGaugeDerivative.fromAction action).eulerLagrange_implies_stationary
    certificate.eulerLagrange

theorem residue_eq_truth_zero
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    (DiscreteGaugeDerivative.fromAction action).residue path =
      .zero Fact.Truth :=
  cubicSplineBalanced_residue_eq_truth_zero certificate.cubic_balanced

end LanczosCubicSpline

def splineSufficient
    (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  (DiscreteGaugeDerivative.fromAction action).residue path =
    .zero Fact.Truth

theorem law_of_spline_sufficiency
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (certificate : LanczosCubicSpline action path) :
    splineSufficient action path :=
  certificate.residue_eq_truth_zero

def closedFlatLanczosCertificate
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (h : action.closedFlatAt path) :
    LanczosCubicSpline action path where
  tridiagonalResidual := cubicSplineResidual action path
  splineResidual := cubicSplineResidual action path
  sameResidual := by
    intro variation
    rfl
  solved := by
    intro variation
    have hs :
        (DiscreteGaugeDerivative.fromAction action).gauge.stationaryAt path :=
      FrechetGauge.fromAction_stationaryAt_of_flatAt h.right
    have hel :
        (DiscreteGaugeDerivative.fromAction action).eulerLagrange path :=
      (DiscreteGaugeDerivative.fromAction action).stationary_implies_eulerLagrange
        hs
    exact hel variation
  matchesGauge := by
    intro variation
    rfl
  admits := h.left

def truthTerminalAction : FiniteGaugeAction where
  segmentCost := fun _ _ => 0

def truthTerminalPath : FiniteGaugePath where
  source := .zero Fact.Truth
  slip := .zero Fact.Truth
  target := .zero Fact.Truth

theorem truthTerminalAction_closedFlatAt
    (path : FiniteGaugePath) :
    truthTerminalAction.closedFlatAt path := by
  constructor
  · rfl
  · intro slip'
    rfl

def truthTerminalLanczos :
    LanczosCubicSpline truthTerminalAction truthTerminalPath :=
  closedFlatLanczosCertificate
    truthTerminalAction
    truthTerminalPath
    (truthTerminalAction_closedFlatAt truthTerminalPath)

theorem truthTerminal_residue_eq_truth_zero :
    (DiscreteGaugeDerivative.fromAction truthTerminalAction).residue
      truthTerminalPath = .zero Fact.Truth :=
  law_of_spline_sufficiency truthTerminalLanczos

end Measurement
