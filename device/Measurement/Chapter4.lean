import Measurement.Chapter3

namespace Measurement


structure Indirection (σ : Type u) where
  before : σ
  after : Type (u+1)

structure Event (σ : Type u) where
  now:  Indirection σ
  value: Invariant σ now.after

structure Commutator (σ : Type u) (τ : Type (v+1)) where
  left: Event σ
  right: Friction Event τ

structure TotalVariation (σ : Type u) (τ : Type (v+1)) where
  first: Indirection σ
  second: Commutator σ τ

abbrev Refinement (σ : Type u)(τ : Type (u+1)) := TotalVariation σ τ


structure Sensor (σ : Type u) where
  reading:   Friction Indirection σ
  stimuli:   Phenomenon σ reading.observable.after
  history:   Ledger (Refinement σ reading.observable.after)
  display:   Digitizer σ

namespace Commutator

/-- Boolean form (useful for filtering / computation). -/
def commutes? {σ : Type u} {τ : Type (v+1)} (C : Commutator σ τ) (e : Event τ) : Bool :=
  decide (C.right.count e < C.right.threshold)

end Commutator

namespace Sensor

def event {σ : Type u} (s : Sensor σ) : Event σ :=
  { now := s.reading.observable
  , value  :=
      { description := s.stimuli.sensor
      , model       := s.stimuli.carrier.map
      }
  }

def read? (s : Sensor σ) [DecidableEq σ] [DecidableEq s.reading.observable.after] : Option Nat :=
  if s.reading.admissible s.reading.observable then
    match s.stimuli.sensor.read? with
    | none => none
    | some _ =>
        match s.display.execute? with
        | some val => some val.down
        | none => none
  else
    none

end Sensor

end Measurement
