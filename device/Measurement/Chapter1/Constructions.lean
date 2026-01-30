/-
Measurement/Chapter1/Constructions.lean

Constructions layer (Chapter 1): Lisp operations on Enumeration,
and the concrete nonempty spine TimeSeries := [head, tail].

-/

import Measurement.Chapter1.ZFC


namespace Measurement

/--
Definition 1: Enumeration Map.
-/

structure EnumerationMap (X : Type u) where
  η : X → Nat
  surjective : Function.Surjective η


/--
Definition 2: Enumeration
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
-/
structure DecodingMap (X : Type v) where
  ζ : Nat → Option X







end Measurement
