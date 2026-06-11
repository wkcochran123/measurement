import Measurement.Episode17

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 18__: _The Frechet Approximation_

Episode17 chose `b` by stationarity.  This episode names the finite
Frechet approximation: varying only the middle point gives a first
variation plus a remainder.
-/

structure FiniteGaugeVariation where
  slip : Bullshit

namespace FiniteGaugeVariation

def apply (variation : FiniteGaugeVariation) (path : FiniteGaugePath) :
    FiniteGaugePath :=
  path.withSlip variation.slip

def identity (path : FiniteGaugePath) : FiniteGaugeVariation :=
  { slip := path.slip }

theorem apply_identity (path : FiniteGaugePath) :
    (identity path).apply path = path := by
  rfl

end FiniteGaugeVariation

namespace FiniteGaugeAction

def leftVariation
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  Int.ofNat (action.segmentCost path.source variation.slip) -
    Int.ofNat (action.segmentCost path.source path.slip)

def rightVariation
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  Int.ofNat (action.segmentCost variation.slip path.target) -
    Int.ofNat (action.segmentCost path.slip path.target)

def firstVariation
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  action.leftVariation path variation + action.rightVariation path variation

theorem firstVariation_eq_composedDifference
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) :
    action.firstVariation path variation =
      Int.ofNat (action.composed (variation.apply path)) -
        Int.ofNat (action.composed path) := by
  unfold firstVariation leftVariation rightVariation composed
    FiniteGaugeVariation.apply FiniteGaugePath.withSlip
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  omega

end FiniteGaugeAction

structure FrechetGauge where
  action : FiniteGaugeAction
  linearPart : FiniteGaugePath -> FiniteGaugeVariation -> Int

namespace FrechetGauge

def fromAction (action : FiniteGaugeAction) : FrechetGauge where
  action := action
  linearPart := action.firstVariation

def value (gauge : FrechetGauge) (path : FiniteGaugePath) : Int :=
  Int.ofNat (gauge.action.composed path)

def variedValue
    (gauge : FrechetGauge) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  gauge.value (variation.apply path)

def remainder
    (gauge : FrechetGauge) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Int :=
  gauge.variedValue path variation - gauge.value path -
    gauge.linearPart path variation

def approximates
    (gauge : FrechetGauge) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) : Prop :=
  gauge.remainder path variation = 0

def stationaryAt (gauge : FrechetGauge) (path : FiniteGaugePath) : Prop :=
  forall variation, gauge.linearPart path variation = 0

theorem fromAction_remainder_zero
    (action : FiniteGaugeAction) (path : FiniteGaugePath)
    (variation : FiniteGaugeVariation) :
    (fromAction action).remainder path variation = 0 := by
  unfold remainder variedValue value fromAction
  change
    Int.ofNat (action.composed (variation.apply path)) -
      Int.ofNat (action.composed path) -
        action.firstVariation path variation = 0
  rw [action.firstVariation_eq_composedDifference path variation]
  simp

theorem fromAction_stationaryAt_of_flatAt
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.flatAt path) :
    (fromAction action).stationaryAt path := by
  intro variation
  change action.firstVariation path variation = 0
  rw [action.firstVariation_eq_composedDifference path variation]
  have hv :
      action.composed (variation.apply path) = action.composed path := by
    simpa [FiniteGaugeVariation.apply] using h variation.slip
  rw [hv]
  simp

theorem stationaryAt_zero
    {gauge : FrechetGauge} {path : FiniteGaugePath}
    (h : gauge.stationaryAt path) (variation : FiniteGaugeVariation) :
    gauge.linearPart path variation = 0 :=
  h variation

end FrechetGauge

end Measurement
