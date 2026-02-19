import Measurement.Chapter3

namespace Measurement

structure PartialOrder (σ : Type u) (τ : Type (u+1)) where
  poset : Enumeration (Inversion σ τ)

structure Event (σ: Type u)(τ: Type (u+1)) where
  state : σ
  reading : τ
  deriving DecidableEq

structure Walking (σ : Type u)(τ : Type (u+1)) where
  poset : PartialOrder σ τ
  candidates : Enumeration (Event σ τ)

structure Counting (σ : Type u)(τ : Type (u+1)) where
  ticks: Enumeration (Event σ τ)


/-
These are the symbols of the numbers in order
-/
abbrev NaturalNumbers := Counting Nat (ULift Nat)


namespace Enumeration

/-- Walk until false; if no false encountered, return true. -/
def all {A : Type u} (p : A → Bool) : Enumeration A → Bool
  | .nil        => true
  | .cons a as  => if p a then all p as else false

/-- "Exists" helper (often useful alongside `all`). -/
def any {A : Type u} (p : A → Bool) : Enumeration A → Bool
  | .nil        => false
  | .cons a as  => if p a then true else any p as

end Enumeration

namespace Inversion
/-- `I` admits `(a,b)` iff decoding `b` through `I.inv` yields `a`. -/
def admits {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ]
  [DecidableEq τ]
  (I : Inversion σ τ) (a : σ) (b : τ) : Bool :=
  match Decomposition.decode? I.inv b with
  | none   => false
  | some a' => decide (a' = a)
end Inversion

namespace Walking

def iterate (W : Walking σ τ) :
    Nat → Option τ :=
  fun t =>
    let u' := t.succ
    match Enumeration.ζ W.candidates u' with
    | none   => none
    | some s => some s.reading

def admits {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ]
  [DecidableEq τ]
  (a : σ)
  (b : τ): Bool :=
  (match Enumeration.findPair? (fun p : (σ × τ) => if _h : p.1 = a then some (p.2 = b) else none) with
  | _ => true)

end Walking


namespace PartialOrder

def le {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ]
  [DecidableEq τ]
  (P : PartialOrder σ τ) (a : σ) (b : τ) : Bool :=
  Enumeration.all (fun I : Inversion σ τ => Inversion.admits I a b) P.poset

end PartialOrder


namespace Counting

/-- Add a tick-event to the counting tape. -/
def push {σ : Type u} {τ : Type (u+1)}
  (C : Counting σ τ) (e : Event σ τ) : Counting σ τ :=
  { C with ticks := Enumeration.count C.ticks e }

end Counting

instance {σ : Type u} {τ : Type (u+1)} [DecidableEq σ] [DecidableEq τ] :
    DecidableEq (Event σ τ) :=
by
  intro a b
  cases a with
  | mk aσ aτ =>
    cases b with
    | mk bσ bτ =>
      cases hσ : (decEq aσ bσ) with
      | isTrue h1 =>
        cases hτ : (decEq aτ bτ) with
        | isTrue h2 =>
          exact isTrue (by cases h1; cases h2; rfl)
        | isFalse h2 =>
          exact isFalse (by
            intro h
            cases h
            exact h2 rfl)
      | isFalse h1 =>
        exact isFalse (by
          intro h
          cases h
          exact h1 rfl)

namespace Event

  def arrow {σ : Type u} {τ : Type (u+1)} (e : Event σ τ) : ArrowOfTime σ τ :=
    ArrowOfTime.mk e.state e.reading

  /-
  We can make symbols to measure things with!!
  -/
  def alphabet .{u} {σ : Type u} {τ : Type (u+1)} (e : Event σ τ) : Alphabet τ :=
    Alphabet.mk (Enumeration.cons e.reading Enumeration.nil)

  /-
  We can design instruments to measure events!!
  -/
  def instrument  {σ : Type u} {τ : Type (u+1)} {L : Ledger σ} (e : Event σ τ) : Instrument σ τ :=
    let time := arrow e
    let after := time.after
    let newEvent := Event.mk e.state after
    Instrument.mk (newEvent.alphabet) L

  /-
  We can build devices to plans that measure events!!
  -/
  def device {σ : Type u} {τ : Type (u+1)} {I: Instrument σ τ} (E : Event σ τ)  : Device σ τ :=
    Device.mk I (Decomposition.zip I.ledger.linked_list I.alphabet.symbols) E.arrow

end Event

end Measurement
