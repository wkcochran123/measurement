import Measurement.Chapter3

namespace Measurement


structure Indirection (σ : Type u) where
  after : Type (u+1)
  before : σ

structure Event (σ : Type u) where
  start: σ
  finish:  Indirection σ
  value: Invariant σ finish.after

structure Commutator (σ : Type u) (τ : Type v) where
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

/-- The commutator commutes as long as the relevant event has not yet
    crossed the friction threshold. -/
def commutes {σ : Type u} {τ : Type v} (C : Commutator σ τ) (e : Event τ) : Prop :=
  C.right.count e < C.right.threshold

/-- Boolean form (useful for filtering / computation). -/
def commutes? {σ : Type u} {τ : Type v} (C : Commutator σ τ) (e : Event τ) : Bool :=
  decide (C.right.count e < C.right.threshold)

end Commutator

namespace Sensor

def event {σ : Type u} (s : Sensor σ) : Event σ :=
  { start  := s.reading.observable.before
  , finish := s.reading.observable
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

def ledger {σ : Type u} (s : Sensor σ) : Ledger (Event σ) :=
  let current_event := s.event
  -- We construct a ledger from the singular current event context
  -- In a stateful system, this would involve folding over the history
  let event_list := Enumeration.cons current_event .nil
  { linked_list   := event_list
  , random_access := Enumeration.numbering event_list
  }

end Sensor

end Measurement
