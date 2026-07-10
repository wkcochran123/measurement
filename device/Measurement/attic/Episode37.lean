import Measurement.Episode36

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 37__: _The Finite Operator Joins the Tower_

Episode28 built the bridge `CompiledSPDGalerkinEnergySq`, which equates the
emitted energy-squared of an SPD Galerkin activity to the terminal residual
magnitude of Episode27's `CompletedResidualWeierstrassTower`.  But it never
populated that bridge with a real operator: the only carrier available then was
`Unit`.

This episode plugs the concrete three-rung operator `threeRungSPD` (Episode34)
into that bridge.  Given any completed residual tower and an emitted activity
whose energy matches the terminal residual magnitude, the three-rung SPD becomes
the operator whose energy norm reads the tower's residual.  The squeeze theorem
(`terminalResidualMagnitude_tends_zero`) then drives that finite energy to zero
across the Weierstrass / B-spline refinement stages.

Stated formally:
* `threeRungCompiled` builds a `CompiledSPDGalerkinEnergySq` with
  `spd := threeRungSPD` from a tower, an emitted activity, and the matching
  certificate.
* `threeRung_supported_energySq_zero` / `threeRung_supported_activity_zero`
  re-export Episode28's collapse theorems for the concrete operator: on
  supported data the terminal residual is zero, so the emitted three-rung
  activity has zero energy and (by the Episode34 / Episode35 coercivity) is
  itself the three-rung zero.
* `anchoredCompiled` does the same for Episode35's anchor-coercive operator.

Residue left:
The emitted activity is supplied as data.  A canonical magnitude-faithful
emitter (one whose three-rung energy equals an arbitrary residual magnitude)
needs a one-dimensional scaling carrier; here the match is the consumed
certificate, exactly as Episode28 specified.
-/

/-- Plug the concrete three-rung SPD into Episode28's residual-tower bridge. -/
def threeRungCompiled
    {range : AdmissibleRange} {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed : CompletedResidualWeierstrassTower range scale action path)
    (emittedActivity : Nat -> FiniteGaugeVariation -> threeRungSPD.form.V)
    (hmatch :
      forall n variation,
        (SPDGalerkinActivity.toEnergySqCertificate threeRungSPD).energySq
          (emittedActivity n variation) =
          intActivityMagnitude
            ((completed.residualTower.stageTrace n).terminalResidual variation)) :
    CompiledSPDGalerkinEnergySq range scale action path where
  completed := completed
  spd := threeRungSPD
  emittedActivity := emittedActivity
  emittedEnergySq_matches_terminalResidualMagnitude := hmatch

/-- On supported data the three-rung emitted energy is zero (the terminal
residual vanishes on the elephant support). -/
theorem threeRung_supported_energySq_zero
    {range : AdmissibleRange} {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed : CompletedResidualWeierstrassTower range scale action path)
    (emittedActivity : Nat -> FiniteGaugeVariation -> threeRungSPD.form.V)
    (hmatch :
      forall n variation,
        (SPDGalerkinActivity.toEnergySqCertificate threeRungSPD).energySq
          (emittedActivity n variation) =
          intActivityMagnitude
            ((completed.residualTower.stageTrace n).terminalResidual variation))
    (n : Nat) (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (completed.completion.approximation.tower.stage n).candidates.entries) :
    (SPDGalerkinActivity.toEnergySqCertificate threeRungSPD).energySq
      ((threeRungCompiled completed emittedActivity hmatch).emittedActivity n variation) = 0 :=
  CompiledSPDGalerkinEnergySq.supported_data_energySq_eq_zero
    (threeRungCompiled completed emittedActivity hmatch)
    n
    variation
    hSupport

/-- On supported data the three-rung emitted activity collapses to the
three-rung zero: the residual tower meets the finite operator's nullspace. -/
theorem threeRung_supported_activity_zero
    {range : AdmissibleRange} {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed : CompletedResidualWeierstrassTower range scale action path)
    (emittedActivity : Nat -> FiniteGaugeVariation -> threeRungSPD.form.V)
    (hmatch :
      forall n variation,
        (SPDGalerkinActivity.toEnergySqCertificate threeRungSPD).energySq
          (emittedActivity n variation) =
          intActivityMagnitude
            ((completed.residualTower.stageTrace n).terminalResidual variation))
    (n : Nat) (variation : FiniteGaugeVariation)
    (hSupport :
      variation.slip ∈
        (completed.completion.approximation.tower.stage n).candidates.entries) :
    (threeRungCompiled completed emittedActivity hmatch).emittedActivity n variation =
      threeRungSPD.form.zero :=
  CompiledSPDGalerkinEnergySq.supported_data_activity_eq_zero_of_spd
    (threeRungCompiled completed emittedActivity hmatch)
    n
    variation
    hSupport

/-- The same bridge for Episode35's anchor-coercive operator: the SPD whose
positive-definiteness is sourced by `.white_hole -> .load`. -/
def anchoredCompiled
    {range : AdmissibleRange} {scale : ApproximationScale}
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (completed : CompletedResidualWeierstrassTower range scale action path)
    (emittedActivity : Nat -> FiniteGaugeVariation -> anchoredSPD.form.V)
    (hmatch :
      forall n variation,
        (SPDGalerkinActivity.toEnergySqCertificate anchoredSPD).energySq
          (emittedActivity n variation) =
          intActivityMagnitude
            ((completed.residualTower.stageTrace n).terminalResidual variation)) :
    CompiledSPDGalerkinEnergySq range scale action path where
  completed := completed
  spd := anchoredSPD
  emittedActivity := emittedActivity
  emittedEnergySq_matches_terminalResidualMagnitude := hmatch

end Measurement
