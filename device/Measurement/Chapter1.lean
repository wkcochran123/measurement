/-
Measurement/Chapter1.lean
Facts

There are four definitions per chapter in the accompanying description.  These
correspond to
o Invariant:     Something that seems to exist
o Instrument:    Metaphysical description of the invariant
o Device:        The representation of a finite process that coulc measure
                 the invariant
o Closure:       The general description of the mathematical container of
                 the invariant


Conventions:

Universe Number:     The η/ζ the compiler uses to understand the ledger of readings
                     built during compilation
η                    The "lookup map" Given a symbol, get any location of that symbol in a list.
ζ                    Given a spot in a list, what is the symbol there?


Chapter 1 discuss the foundations of time and counting.  It identifies the ArrowOfTime
as the concept of before and after.  Concepts "before" ar of universe Type u.  Concepts
"after" are of universe Type u+1.  The universe evolves through time.

There is one assumption that runs through the code, the decidablility of equality between
abstract symbols.  Please refere to section 1.1 on the reasoning.  This is evidenced by
[DecidableEq σ] and [DecidableEq τ] appearing in the type signatures of many functions.

Further, any future conmputation is _noncomputable_.  Please refere to Section 1.1 for
the reasoning.  Basically, there is no computation that predicts the future exactly,
so we prevent Lean from trying.
-/

import Std
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic



namespace Measurement

/-
There are two types of values, physical and metaphysical.
-/
universe u v

/-
Axiom 1: The Axiom of Distinquishability
-/

class Distinguishable (σ : Type u) : Type (u+1) where
  inst : DecidableEq σ

/--
Definition 1: ArrowOfTime

This structure holds the type of two symbols, one that happened
"before" now and one that will happend "after" now. The event
σ happens before the reading τ.
-/
structure ArrowOfTime (σ : Type u)(τ : Type (u+1)) where
  before: σ
  after: τ
  deriving DecidableEq


/--
Definition 2: Enumeration

The most simple mathematical act is to count.  Counting
does not necessarily take time.
-/
inductive Enumeration (A : Type u) : Type u
  | nil : Enumeration A
  | cons : A → Enumeration A → Enumeration A
deriving instance DecidableEq for Enumeration

/--
Definition 3: DecodingMap

The decoding map is the thing that is made when you count something.
It assigns an ordinal to a thing.
-/
structure Numbering (σ : Type u) where
  pairs : Enumeration (Nat × σ)
  swaps : Enumeration (σ × Nat)
  deriving DecidableEq


/--
Definition 4: Ledger

A Ledger is a list of things that have been counted (the linked_list)
and the ordinal lookup index for those objects.  It is just a list
with symbols on it that you can randomly access by entry number.
These data comprise _facts_.
-/
structure Ledger (σ : Type u) : Type u where
  linked_list : Enumeration σ
  random_access : Numbering σ
  deriving DecidableEq



/-
Coda: Friction
-/

class Friction (E : Type u → Type v) (σ : Type u) : Type (max u v + 1) where
  count : E σ → Nat
  threshold : Nat
  observable : E σ

/-
**************************************************************
Code:

This software uses discrete definitions of _many_ common concepts
from mathematics all built from the idea of counting.
-/

namespace ArrowOfTime

/--
To elapse is to go forward in time.
-/
def elapse {X : Type u} {Y : Type (u+1)} (A : ArrowOfTime X Y) : Option Y :=
  some A.after

/--
One cannot relive the past.
Lean does a _really_ good job of making sure you could not do this anyway, but,
just to underline the point.
-/
def relive {X : Type u} : Option X :=
  none

end ArrowOfTime



namespace Enumeration

variable {A : Type u}

/-- Append enumerations (needed to flatten a 2D shape). -/
def append {A : Type u} : Enumeration A → Enumeration A → Enumeration A
  | .nil, ys => ys
  | .cons a as, ys => .cons a (append as ys)

def count : Enumeration A → A → Enumeration A
  | xs, a => append xs (.cons a .nil)

def relation {X : Type u} : Enumeration X → Nat → Enumeration (Nat × X)
  | .nil,      _ => .nil
  | .cons x xs, n => .cons (n, x) (relation xs (n + 1))

def map {A : Type u} {B : Type v} (f : A → B) : Enumeration A → Enumeration B
  | .nil => .nil
  | .cons a as => .cons (f a) (map f as)

end Enumeration


namespace Numbering
def ζ {X : Type u} [DecidableEq X] (dm : Numbering X) (n : Nat) : Option X :=
  let rec find : Enumeration (Nat × X) → Option X
    | .nil => none
    | .cons (idx, sym) tail =>
        if idx = n then some sym else find tail
  find dm.pairs

def η {X : Type u} [DecidableEq X] (dm : Numbering X) (x : X) : Option Nat :=
  let rec find : Enumeration (X × Nat) → Option Nat
    | .nil => none
    | .cons (y, k) xs => if y = x then some k else find xs
  find dm.swaps

def map {X : Type u} {Y : Type v} (f : X → Y) (N : Numbering X) : Numbering Y :=
{ pairs := N.pairs.map (fun p => (p.1, f p.2))
, swaps := N.swaps.map (fun p => (f p.1, p.2))
}

def swap {σ : Type u} {τ : Type v} (N : Numbering (σ × τ)) : Numbering (τ × σ) :=
{ pairs := N.pairs.map (fun p => (p.1, (p.2.2, p.2.1)))  -- (n,(σ,τ)) -> (n,(τ,σ))
, swaps := N.swaps.map (fun p => ((p.1.2, p.1.1), p.2))  -- ((σ,τ),n) -> ((τ,σ),n)
}

def swapProd {σ : Type u} {τ : Type v} (N : Numbering (σ × τ)) : Numbering (τ × σ) :=
{ pairs := Enumeration.map
    (fun p : Nat × (σ × τ) => (p.1, (p.2.2, p.2.1)))
    N.pairs
, swaps := Enumeration.map
    (fun p : (σ × τ) × Nat => ((p.1.2, p.1.1), p.2))
    N.swaps
}

end Numbering

namespace Friction

def admissible (F : Friction E σ) (x : E σ) : Bool :=
  decide (F.threshold ≤ F.count x)

def silence (F : Friction E σ) (x : E σ) : Option (E σ) :=
  if admissible F x then some x else none

end Friction

end Measurement
