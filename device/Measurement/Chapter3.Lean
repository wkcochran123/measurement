import Measurement.Chapter2

namespace Measurement

/--
Definition 11: Inversion

This is _not_ an inversion in the sense of a mathematical inverse.  It is the inversion of a
decomposition.  Given a decomposition, this will invert the order of the pairs in the decomposition.
-/
structure Inversion (σ : Type u) (τ : Type v) where
  inv : Decomposition τ σ

namespace Inversion

def eta {σ : Type u} {τ : Type v} (I : Inversion σ τ) : Nat → Option (τ × σ) :=
  fun n => Enumeration.nth I.inv.pairs n

end Inversion

namespace Enumeration

/-- Map a function over an enumeration. -/
def map {A : Type u} {B : Type v} (f : A → B) : Enumeration A → Enumeration B
  | .nil        => .nil
  | .cons a as  => .cons (f a) (map f as)

def findMap? {A : Type u} {B : Type v} (f : A → Option B) : Enumeration A → Option B
  | .nil        => none
  | .cons a as  =>
      match f a with
      | some b => some b
      | none   => findMap? f as

/-- `indexOf`, but using a user-supplied equality test instead of `DecidableEq`. -/
def indexOfBy {A : Type u} (eqb : A → A → Bool) : Enumeration A → A → Option Nat
  | .nil,        _ => none
  | .cons a as,  x =>
      if eqb a x then
        some 0
      else
        Option.map Nat.succ (indexOfBy eqb as x)


end Enumeration

namespace Decomposition

/-- Swap the components of each pair in a decomposition. -/
def inverse {σ : Type u} {τ : Type v} (D : Decomposition σ τ) : Decomposition τ σ :=
{ pairs :=
    D.pairs.map (fun p : (σ × τ) => (p.2, p.1)) }

def read? {σ : Type u} {τ : Type v} [DecidableEq σ]
    (D : Decomposition σ τ) (s : σ) : Option τ :=
  none

/-- Decode along a decomposition by searching the enumerated pairs. -/
def decode? {τ : Type u} {σ : Type v} [DecidableEq τ]
    (D : Decomposition τ σ) (t : τ) : Option σ :=
  Enumeration.findMap?
    (fun p : (τ × σ) =>
      if h : p.1 = t then
        some p.2
      else
        none)
    D.pairs

end Decomposition

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
