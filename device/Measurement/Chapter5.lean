import Measurement.Chapter4

namespace Measurement

class CORRELANT
    (symbol: Type now)
    (event: Type (now+1))
    [DISTINGUISHABLE symbol event]
    (number : symbol)
    (value : symbol -> symbol -> Bool)
    [COUNTABLE symbol event number value]
    (domain : symbol -> symbol -> Bool)
    (transform : symbol -> Option (ULift.{now+1, now} symbol))
    [LOCAL symbol event number value domain transform]
    (mapping : symbol)
    (first_variation : symbol → symbol → Bool)
    [ADMISSIBLE symbol event number value domain transform mapping first_variation]
    second_variation : symbol → Option (ULift.{now+2, now+1} symbol)
      where

  correlates? : symbol -> event -> Bool
  dψ : symbol

/-
universe u v w

structure History (σ : Type u) where
  elements: Numbering σ
  ordering: Numbering (Ledger σ)

structure Interpolation (σ: Type u)(τ: Type (u+1)) where
  anchors: Ledger (Event σ)
  values: Ledger (Invariant σ τ)

structure Correllance (σ : Type u) (τ : Type (v+1)) where
  first: Distinguishable (Event σ)
  second: Distinguishable (Event τ)

structure Behavior (σ : Type u) (τ : Type (u+1)) where
  evidence : Numbering (Interpolation σ τ)
  carrier : Carrier σ τ
  phenomenon : Phenomenon σ τ

structure Sensor (σ : Type u) (τ : Type (u+1)) where
  reading:   Friction (Indirection σ) τ
  history:   Friction Ledger (Event σ)
  stimuli:   Friction (Behavior σ) τ
  display:   Digitizer σ




namespace Sensor

def φ {σ : Type u} {τ : Type (u+1)} (s : Sensor σ τ) (t : Rat)[DecidableEq σ] : Option Rat :=
  let event := match (s.history.observable (Ledger (Event σ))).random_access.η ⌊ t ⌋ with
    | none => sorry
    | some e => e
  if
  event.description.admissible event then
    some (event.description)

def event {σ : Type u} {τ : Type (u+1)} (s : Sensor σ τ) : Distinguishable (Event σ) :=

def read? (s : Sensor σ τ) [DecidableEq σ] : Option Rat :=



end Sensor

-/

end Measurement
