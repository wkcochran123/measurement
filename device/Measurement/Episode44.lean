import Measurement.Episode43

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 44__: _The Integrator_

The chain the reviewer named --
  finite activity encoding -> apparatus evaluator -> ledger entry
  -> obstruction certificate -> finite gauge equations / EL residue
-- terminates here, at the EL residue.  Its terminal object already exists:
`CubicGaugeVariation.coupledCubicDifference` (Episode24) is the change in the
cubic action when both middle nodes move,

  coupledCubicDifference action path variation
    = cubicCost (variation.apply path) - cubicCost path
    = leftMiddleResidual + rightMiddleResidual + mixedCubicCoupling   (Ep24/31)

The two middle residuals are the discrete Euler-Lagrange equations; the mixed
cubic coupling is the non-abelian self-interaction (the `A ∧ A` of Episode4's
`F = dF + A ∧ A`).  The discrete gauge equation is `coupledCubicDifference = 0`.

This episode builds the integrator -- the apparatus reading of that residue --
and turns the crank.  Run it on `y = x` (the identity variation, which
reproduces the path): the reading is `0`, the trivial on-shell solution, the
ledger's physical record.  Run it off-shell: the reading is the residual the
action actually changed by, and it is provably nonzero when the cost changes.
A concrete run reads `0` on the unchanged path and `2` on a kicked one.

What this is: the discrete gauge / Euler-Lagrange equation, realized as the
apparatus's reading, with its on-shell solutions the realizable ledger entries
and its well-posedness (Episode42's coercivity, once the anchor pins the
nullspace) the obstruction certificate.  Yang-Mills from admissibility, at the
discrete, finite level.

What this is NOT (the honest ceiling): not continuum Yang-Mills (the residual
tower's limit is still a door, Ep27/38), not the mass gap (coercivity of the
discrete second variation is finite well-posedness, not the continuum spectrum),
and not an SU(N) gauge group (color/flavor remain inert, per the audit).  This
is the discrete EL equation of a cubic-coupled gauge action, interpreted as YM.
-/

/-- The integrator: the apparatus reads the gauge action's Euler-Lagrange
residue (the change in action under the variation). -/
def gaugeReading
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Nat :=
  intActivityMagnitude (CubicGaugeVariation.coupledCubicDifference action path variation)

/-- The discrete gauge (Euler-Lagrange) equation: the action is stationary
under the variation. -/
def IsGaugeSolution
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : Prop :=
  CubicGaugeVariation.coupledCubicDifference action path variation = 0

/-- `y = x`: the identity variation reproduces the path's own middle nodes. -/
def identityVariation (path : CubicGaugePath) : CubicGaugeVariation :=
  { middleLeftSlip := path.middleLeft, middleRightSlip := path.middleRight }

/-- RUN 1 (`y = x`): on the unchanged configuration the action does not change,
so the integrator reads `0` -- the trivial on-shell solution. -/
theorem identity_is_solution
    (action : FiniteGaugeAction) (path : CubicGaugePath) :
    IsGaugeSolution action path (identityVariation path) := by
  have happly :
      CubicGaugeVariation.apply (identityVariation path) path = path := by
    cases path; rfl
  unfold IsGaugeSolution CubicGaugeVariation.coupledCubicDifference
  rw [happly]; omega

theorem gaugeReading_identity_zero
    (action : FiniteGaugeAction) (path : CubicGaugePath) :
    gaugeReading action path (identityVariation path) = 0 := by
  have h :
      CubicGaugeVariation.coupledCubicDifference action path (identityVariation path) = 0 :=
    identity_is_solution action path
  unfold gaugeReading
  rw [h]; decide

/-- RUN 2 (detection): the integrator reads nonzero exactly when the action
changes, so it is not vacuously `0` -- it measures off-shell deviation. -/
theorem detects_nonstationary
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation)
    (h :
      CubicGaugePath.cubicCost action (variation.apply path) ≠
        CubicGaugePath.cubicCost action path) :
    ¬ IsGaugeSolution action path variation := by
  intro hsol
  have hz :
      CubicGaugeVariation.coupledCubicDifference action path variation = 0 := hsol
  unfold CubicGaugeVariation.coupledCubicDifference at hz
  simp only [Int.ofNat_eq_natCast] at hz
  apply h
  omega

/-- The integrator's reading IS the discrete gauge equation's content: the two
middle Euler-Lagrange residuals plus the cubic self-coupling (Episode24). -/
theorem reading_is_EL_plus_coupling
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    CubicGaugeVariation.coupledCubicDifference action path variation =
      CubicGaugePath.leftMiddleResidual
          action path (CubicGaugeVariation.leftVariation variation) +
        CubicGaugePath.rightMiddleResidual
          action path (CubicGaugeVariation.rightVariation variation) +
          CubicGaugeVariation.mixedCubicCoupling action path variation :=
  CubicGaugeVariation.coupledCubicDifference_eq_left_right_plus_mixed
    action path variation

/-
Concrete crank-turn.  A discriminating action: cost `0` between nodes of the same
constructor-tag, `1` otherwise.  On a flat path (all `.zero` nodes) the identity
reads `0`; kicking a middle node to a `.one` node reads `2` (two edges change).
-/

abbrev Bullshit0 := Bullshit.{0, 0, 0, 0}
abbrev FiniteGaugeAction0 := FiniteGaugeAction.{0, 0, 0, 0, 0, 0, 0, 0}
abbrev CubicGaugePath0 :=
  CubicGaugePath.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
abbrev CubicGaugeVariation0 := CubicGaugeVariation.{0, 0, 0, 0, 0, 0, 0, 0}

def tag : Bullshit0 -> Nat
  | .zero _ => 0
  | .one _ _ _ _ _ => 1
  | .rest _ _ _ _ _ _ _ _ _ _ => 2

def discriminatingAction : FiniteGaugeAction0 :=
  { segmentCost := fun x y => if tag x = tag y then 0 else 1 }

def node0 : Bullshit0 := .zero Fact.Truth

def node1 : Bullshit0 :=
  .one Fact.Truth (Number.zero Fact.Truth)
    (CompilerTape.boot Fact.Truth (Unit : Type))
    (CompilerTape.boot Fact.Truth (Unit : Type))
    (.zero Fact.Truth)

def flatPath : CubicGaugePath0 :=
  { source := node0, middleLeft := node0, middleRight := node0, target := node0 }

def unchangedVariation : CubicGaugeVariation0 :=
  { middleLeftSlip := node0, middleRightSlip := node0 }

def kickVariation : CubicGaugeVariation0 :=
  { middleLeftSlip := node1, middleRightSlip := node0 }

def identityGaugeReading : Nat :=
  gaugeReading.{0, 0, 0, 0} discriminatingAction flatPath unchangedVariation

def kickedGaugeReading : Nat :=
  gaugeReading.{0, 0, 0, 0} discriminatingAction flatPath kickVariation

/-- RUN 3 (concrete): the integrator reads `0` on the unchanged path and `2` on
the kicked one -- the instrument produces a real, nonzero physical distinction. -/
theorem concrete_runs :
    identityGaugeReading = 0 ∧ kickedGaugeReading = 2 := by
  refine ⟨?_, ?_⟩ <;> decide

end Measurement
