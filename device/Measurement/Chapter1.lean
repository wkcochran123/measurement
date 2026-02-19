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



namespace Measurement

/-
There are two types of values, physical and metaphysical.
-/
universe u v

/--
Definition 1: ArrowOfTime

This structure holds the type of two symbols, one that happened
"before" now and one that will happend "after" now.
-/
structure ArrowOfTime (X : Type u)(Y : Type (u+1)) where
  before: X
  after: Y

/--
Definition 2: Enumeration

The most simple mathematical act is to count.  Counting
does not necessarily take time.
-/
inductive Enumeration (A : Type u) : Type u
  | nil : Enumeration A
  | cons : A → Enumeration A → Enumeration A

/--
Definition 3: DecodingMap

The decoding map is the thing that is made when you count something.
It assigns an ordinal to a thing.
-/
structure DecodingMap (X : Type v) where
  ζ : Nat → Option X


/--
Definition 4: Ledger

A Ledger is a list of things that have been counted (the linked_list)
and the ordinal lookup index for those objects.  It is just a list
with symbols on it that you can randomly access by entry number.
These data comprise _facts_.
-/
structure Ledger (X : Type u) : Type u where
  linked_list : Enumeration X
  random_access : DecodingMap X



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

def η [DecidableEq A] : Enumeration A → A → Option Nat
  | .nil,      _ => none
  | .cons a t, x => if a = x then some 0 else (η t x).map Nat.succ

def ζ : Enumeration A -> Nat -> Option A
  | .nil,      _     => none
  | .cons a _, 0     => some a
  | .cons _ t, n + 1 => ζ t n

/-- Append enumerations (needed to flatten a 2D shape). -/
def append {A : Type u} : Enumeration A → Enumeration A → Enumeration A
  | .nil, ys => ys
  | .cons a as, ys => .cons a (append as ys)

def count : Enumeration A → A → Enumeration A
  | xs, a => append xs (.cons a .nil)

end Enumeration


end Measurement
