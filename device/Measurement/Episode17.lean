import Measurement.Episode16

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 17__: _The Stationary Reader_

Episode16 made the middle point admissible: the direct reading `a -> c`
can be compared with the composed reading `a -> b -> c`.

This episode names two constraints, and they are not the same.

`stationaryAt` says the chosen slip is a minimum of the composed action.
`flatAt` says the composed action cannot detect the slip coordinate at all.
Thus:

* `reducibleSlip = admits ∧ minimum-stationary`
* `closedFlatAt  = admits ∧ gauge-flat`

The final residue theorem intentionally uses the stronger `closedFlatAt`.
-/

structure FiniteGaugePath where
  source : Bullshit
  slip : Bullshit
  target : Bullshit

namespace FiniteGaugePath

def withSlip (path : FiniteGaugePath) (slip : Bullshit) : FiniteGaugePath :=
  { path with slip := slip }

end FiniteGaugePath

structure FiniteGaugeAction where
  segmentCost : Bullshit -> Bullshit -> Nat

namespace FiniteGaugeAction

def direct (action : FiniteGaugeAction) (path : FiniteGaugePath) : Nat :=
  action.segmentCost path.source path.target

def composed (action : FiniteGaugeAction) (path : FiniteGaugePath) : Nat :=
  action.segmentCost path.source path.slip +
    action.segmentCost path.slip path.target

def admits (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.direct path = action.composed path

def stationaryAt (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  forall slip' : Bullshit,
    action.composed path <= action.composed (path.withSlip slip')

def flatAt (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  forall slip' : Bullshit,
    action.composed (path.withSlip slip') = action.composed path

def closedFlatAt (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.admits path /\ action.flatAt path

def reducibleSlip (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.admits path /\ action.stationaryAt path

theorem flatAt_stationaryAt
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.flatAt path) :
    action.stationaryAt path := by
  intro slip'
  rw [h slip']
  exact Nat.le_refl _

theorem closedFlatAt_admits
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    action.admits path :=
  h.left

theorem closedFlatAt_flatAt
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    action.flatAt path :=
  h.right

theorem closedFlatAt_reducibleSlip
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    action.reducibleSlip path :=
  ⟨h.left, action.flatAt_stationaryAt h.right⟩

theorem reducibleSlip_admits
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.reducibleSlip path) :
    action.admits path :=
  h.left

theorem reducibleSlip_stationary
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.reducibleSlip path) :
    action.stationaryAt path :=
  h.right

end FiniteGaugeAction

end Measurement
