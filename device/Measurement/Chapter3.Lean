import Measurement.Chapter2

namespace Measurement

/--
Definition 11: Inversion

This is _not_ an inversion in the sense of a mathematical inverse.  It is the inversion of a
decomposition.  Given a decomposition, this will invert the order of the pairs in the decomposition.
-/
structure Inversion (σ : Type u) (τ : Type v) where
  inv : Decomposition τ σ

namespace Enumeration

def map {A : Type u} {B : Type v} (f : A → B) : Enumeration A → Enumeration B
  | .nil        => .nil
  | .cons a as  => .cons (f a) (map f as)

def findMap? {A : Type u} {B : Type v} (f : A → Option B) : Enumeration A → Option B
  | .nil        => none
  | .cons a as  =>
      match f a with
      | some b => some b
      | none   => findMap? f as

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

namespace Inversion

def η {σ : Type u} {τ : Type v} (I : Inversion σ τ) : Nat → Option (τ × σ) :=
  fun n => Enumeration.nth I.inv.pairs n

end Inversion


/--
Definition 12: Carrier

Metaphysical device responsible for event arrival.
-/

structure Carrier (σ : Type u) (τ : Type v) where
  instrument: Instrument σ τ
  model: TuringDevice σ τ
  map: Inversion σ τ

namespace Carrier

noncomputable def recv? {σ : Type u} {τ : Type v}
  [DecidableEq σ] [DecidableEq τ]
  (C : Carrier σ τ) (x : σ) : Option τ :=

  match C.model.decomposition.inverse.decode? x with
  | none => none
  | some y =>
      match C.map.inv.decode? y with
      | none   => none
      | some _ => some y

end Carrier

namespace Device

/-- Promote a `Device` to its implied metaphysical `Carrier`.
    The computational model is the most expressive finite object available here:
    the device itself (a `TuringDevice`). The inversion map is the device's
    own decomposition viewed as an `Inversion`. -/
  def getCarrier {σ : Type u} {τ : Type v} (D : Device σ τ) : Carrier σ τ :=
{ instrument := D.instrument
  model      := D
  map        := { inv := D.decomposition } }

end Device

/--
Definition 13: RealCarrier

This carrier can carry the description of a real number
-/
abbrev DopplerCarrier := Carrier Nat Nat





/--
Definition 14: Phenomenon

A phenomenon is an observered experience.  It is detected
by a sensor and must be carried by a carrier.
-/

structure Phenomenon (σ : Type u) (τ : Type v) where
  sensor : Device σ τ
  carrier : Carrier σ τ


/--
Definition 15: Event

An event is a distinquished occurence.  It is
distinguished by its symbol, σ, which may or may not
come from an alphabet.
-/
structure Event (σ : Type u) where
  symbol : σ

instance {σ : Type u} [DecidableEq σ] : DecidableEq (Event σ)
| ⟨s₁⟩, ⟨s₂⟩ =>
  match decEq s₁ s₂ with
  | isTrue h  => isTrue (by cases h; rfl)
  | isFalse h => isFalse (by
      intro h'
      cases h'
      exact h rfl)

namespace Event

noncomputable def value (e : Event σ) (x : ℝ) : Option σ :=
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

structure Invariant (σ : Type u) (τ : Type v) where
  evidence : Device σ τ
  model    : Inversion σ τ
  survivor : (σ × τ) → Option τ

namespace Invariant

noncomputable def admissible {σ : Type u} {τ : Type v}
    [DecidableEq σ]
    (I : Invariant σ τ) (e : σ) : Option τ :=
  match I.model.inv.inverse.decode? e with
  | none   => none
  | some y => I.survivor (e, y)

end Invariant


end Measurement
