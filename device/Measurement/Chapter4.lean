import Measurement.Chapter3

namespace Measurement

structure PartialOrder (σ : Type u) (τ : Type (v+1)) where
  poset : Enumeration (Inversion σ τ)
  ordering : Numbering (Inversion σ τ)

structure Event (σ: Type u)(τ: Type (u+1)) where
  state : σ
  reading : τ
  deriving DecidableEq

structure Walking (σ : Type u)(τ : Type (v+1)) where
  poset : PartialOrder σ τ
  candidates : Numbering (Event σ τ)

structure Counting (σ : Type u)(τ : Type (v+1)) where
  ticks: Enumeration (Event σ τ)


/-
These are the symbols of the numbers in order
-/
abbrev NaturalNumbers := Counting Nat (ULift Nat)
deriving instance DecidableEq for Counting

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


namespace Counting

def enumerate (n:NaturalNumbers): Enumeration Nat :=
  n.ticks.map (fun e => e.state)

def natural_instrument
  (c : NaturalNumbers) : Instrument σ (ULift Nat) :=
    let symbols := c.ticks.map (fun e => e.reading)
    let alpha := Alphabet.mk symbols
    let list := Enumeration.nil
    let ledger := Ledger.mk list list.numbering
    Instrument.mk ledger alpha

def push {σ : Type u} {τ : Type (u+1)}
  (C : Counting σ τ) (e : Event σ τ) : Counting σ τ :=
  { C with ticks := Enumeration.count C.ticks e }

end Counting

namespace Inversion
/-- `I` admits `(a,b)` iff decoding `b` through `I.inv` yields `a`. -/
def admits {σ : Type u} {τ : Type v}
  [DecidableEq σ]
  [DecidableEq τ]
  (I : Inversion σ τ) (a : σ) (b : τ) : Bool :=
  match Decomposition.decode? I.inv b with
  | none   => false
  | some a' => decide (a' = a)

def event {σ : Type u}{τ : Type (v+1)} {υ : Type v} (i: Inversion σ υ) (e: Event σ τ): Event σ τ :=
  let new_tau :=
end Inversion

namespace PartialOrder

def le {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ]
  [DecidableEq τ]
  (P : PartialOrder σ τ) (a : σ) (b : τ) : Bool :=
  Enumeration.all (fun I : Inversion σ τ => Inversion.admits I a b) P.poset

def walking {σ : Type u} {τ : Type (u+1)} (p: PartialOrder σ τ) Walking σ τ :=
  Walking.mk {p }

end PartialOrder

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
    let alpha := e.alphabet
    let list := Enumeration.cons e.state Enumeration.nil
    let decoder := list.decoder
    let ledger := Ledger.mk list decoder
    Instrument.mk ledger alpha

  /-
  We can build devices to plans that measure events!!
  -/

  def invariant {σ : Type u} {τ : Type (u+1)} (e : Event σ τ) (l : Ledger σ)[DecidableEq σ] [DecidableEq τ] : Invariant σ τ :=
    let description := e.instrument (L := l)
    let device := description.device
    let model := device.decomposition.invert e

    Invariant.mk device model

end Event



namespace Walking

def admits {σ : Type u} {τ : Type (u+1)}
  [DecidableEq σ]
  [DecidableEq τ]
  (a : σ)
  (b : τ): Bool :=
  (match Enumeration.findPair? (fun p : (σ × τ) => if _h : p.1 = a then some (p.2 = b) else none) with
  | _ => true)

end Walking



namespace Counting

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


namespace Decomposition
def invert {σ : Type u} {τ : Type (u+1)} (d : Decomposition σ τ) (e : Event σ τ)
  [DecidableEq σ] [DecidableEq τ]: Inversion σ τ :=
  -- Step 1: Use η to identify the state's entry point in the decomposition
  let current_pair := (e.state, e.reading)
  let before := d.pairs.η current_pair

  -- Step 2: Use ζ to identify the reading's exit point
  let after := match before with
  | none => sorry
  | some n => match d.ζ n with
              | none => sorry
              | some pair => pair.1

  -- Step 3: Finally look up the symbol for before in the enumeration
  let before := match before with
  | none => sorry
  | some n => match d.pairs.ζ n with
              | none => sorry
              | some pair => pair.2

  let inference_arrow := ArrowOfTime.mk after before

  Inversion.mk d.swap inference_arrow
end Decomposition

end Measurement
