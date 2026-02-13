
/-
Measurement/Chapter1.lean

See text for description of the contents of this file.
-/

import Std
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic



namespace Measurement

/--
Definition 1: Enumeration Map.

Step 1: Count your objects
-/

structure EnumerationMap (X : Type u) where
  η : X → Nat
  surjective : Function.Surjective η


/--
Definition 2: Enumeration

Step 2: List them as you count.
-/
inductive Enumeration (A : Type u) : Type u
  | nil : Enumeration A
  | cons : A → Enumeration A → Enumeration A


namespace Enumeration

variable {A : Type u}

def nth : Enumeration A -> Nat -> Option A
  | .nil,      _     => none
  | .cons a _, 0     => some a
  | .cons _ t, n + 1 => nth t n

def last : Enumeration A -> Option A
  | .nil        => none
  | .cons a .nil => some a
  | .cons _ t   => last t

def len : Enumeration A -> Nat
  | .nil      => 0
  | .cons _ t => len t + 1

def append : Enumeration A -> Enumeration A -> Enumeration A
  | .nil,        ys => ys
  | .cons a as,  ys => .cons a (append as ys)

def rev : Enumeration A -> Enumeration A
  | .nil      => .nil
  | .cons a t => append (rev t) (.cons a .nil)

inductive Prefix {A : Type u} : Enumeration A -> Enumeration A -> Prop
  | nil  (t) : Prefix .nil t
  | cons (a) (s t) : Prefix s t -> Prefix (.cons a s) (.cons a t)

/-- Lexicographic `<=` on enumerations, with equality only if they end together. -/
def leLex {A : Type u} [Ord A] : Enumeration A → Enumeration A → Bool
  | .nil,       .nil        => true
  | .nil,       .cons _ _   => false
  | .cons _ _,  .nil        => false
  | .cons a as, .cons b bs  =>
      match compare a b with
      | Ordering.lt => true
      | Ordering.gt => false
      | Ordering.eq => leLex as bs

variable {A : Type u}

def snoc : Enumeration A → A → Enumeration A
  | xs, a => append xs (.cons a .nil)

def indexOf [DecidableEq A] : Enumeration A → A → Option Nat
  | .nil,      _ => none
  | .cons a t, x => if a = x then some 0 else (indexOf t x).map Nat.succ

end Enumeration


/--
Definition 3: Decoding Map

With a list, you can find the nth element, if there is one.
-/
structure DecodingMap (X : Type v) where
  ζ : Nat → Option X


/--
Definition 4: Ledger

Now, we make a linked list to store the objects we are counting.
-/
structure Ledger (X : Type u) : Type u where
  head : X
  tail : Enumeration X

namespace Ledger

variable {X : Type u}

def toEnum (L : Ledger X) : Enumeration X :=
  .cons L.head L.tail

def first (L : Ledger X) : X :=
  L.head

def rest (L : Ledger X) : Nat -> Option X :=
  fun n => Enumeration.nth L.tail n

def last (L : Ledger X) : X :=
  match Enumeration.last (L.toEnum) with
  | some x => x
  | none   => L.head

def index (L : Ledger X) : Nat -> Option X :=
  fun n =>
    match n with
    | 0     => some L.head
    | n + 1 => Enumeration.nth L.tail n

def reverse (L : Ledger X) : Ledger X :=
  match Enumeration.rev (L.toEnum) with
  | .nil => { head := L.head, tail := .nil }
  | .cons h t => { head := h, tail := t }

def size (L : Ledger X) : Nat :=
  Enumeration.len (L.toEnum)

def le {X : Type u} [Ord X] (L₁ L₂ : Ledger X) : Bool :=
  Enumeration.leLex (toEnum L₁) (toEnum L₂)

end Ledger


end Measurement
