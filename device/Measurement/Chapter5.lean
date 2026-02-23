import Measurement.Chapter4

namespace Measurement

universe u v w

structure History (σ : Type u) where
  elements: Numbering σ
  ordering: Numbering (Ledger σ)

structure Interpolation (σ: Type u)(τ: Type (u+1)) where
  anchors: Ledger (Event σ)
  values: Ledger (Invariant σ τ)

structure Path (σ : Type u) (τ : Type (u+1)) where
  history: History σ
  interpolation: Interpolation σ τ

structure Behavior (σ : Type u) (τ : Type (u+1)) where
  evidence : Numbering (Path σ τ)
  carrier : Carrier σ τ
  phenomenon : Phenomenon σ τ



namespace Behavior
def admissible
  (B : Behavior σ τ)
  (E : Event τ) : Bool :=
  -- 1. Access the friction defined on the sensor within the phenomenon
  let sensor_friction := B.carrier.

  -- 2. Verify if the event passes the friction threshold
  -- Note: This treats the event E as an observable stimulus
  if sensor_friction.admissible (Indirection.mk (Type (u+2)) E.start) then
    /-
    3. Validate against the Evidence numbering.
       We check if the Path corresponding to this event exists in our records.
    -/
    match B.evidence.η (B.phenomenon.carrier.ordering) with
    | some _ => true
    | none   => false
  else
    false


end Behavior

end Measurement
