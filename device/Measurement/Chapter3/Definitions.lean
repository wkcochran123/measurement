import Measurement.Chapter3.Constructions


namespace Measurement

universe u v w

structure Calibration (σ : Type u) (τ : Type v) where
  measurment: Decomposition σ τ
  reference: Decomposition τ σ
  read : σ → Option τ

namespace Calibration

def judgeEq {σ : Type u} {τ : Type v} [DecidableEq τ]
    (C : Calibration σ τ) (a b : σ) : Bool :=
  match C.read a, C.read b with
  | some x, some y => decide (x = y)
  | _, _           => false

end Calibration


structure Phenomenon (σ : Type u) (τ : Type v) where
  invariant : Inversion σ τ
  calibration : Calibration σ τ


/--
An Event is a single symbol from the alphabet of a Phenomenon.
NOTICE: σ is potentially uncountable!  Handle with care!
-/
structure Event (σ : Type u) where
  symbol : σ

namespace Phenomenon

/--
The Enumeration of a Phenomenon is the Map (η) that assigns
each Event symbol to a unique Natural number (the ledger index).
-/
def enumeration {σ : Type u} {τ : Type v} [DecidableEq τ]
    (decode : Event σ → Option τ) (e : Enumeration (Event σ)) :
    Event σ → Option Nat :=
  fun event =>
    Enumeration.indexOfBy
      (fun a b =>
        match decode a, decode b with
        | some x, some y => decide (x = y)
        | _, _           => false)
      e
      event

end Phenomenon

end Measurement
