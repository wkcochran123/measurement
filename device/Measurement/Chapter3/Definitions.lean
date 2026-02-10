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


structure Event (σ : Type u) where
  symbol : σ

namespace Event

noncomputable def eval (e : Event σ) (x : ℝ) : Option σ :=
  if h : (0 < x ∧ x ≤ 1) then
    some e.symbol
  else
    none

end Event

namespace Phenomenon

/-- Unless I miss my guess, this can be a real-valued function
on the positive real numbers-/
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
