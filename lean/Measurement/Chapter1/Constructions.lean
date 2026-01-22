/-
Measurement/Chapter1/Constructions.lean

Constructions layer (Chapter 1): Lisp operations on Enumeration,
and the concrete nonempty spine TimeSeries := [head, tail].

-/

import Measurement.Chapter1.ZFC


namespace Measurement

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

variable {A : Type u}

def snoc : Enumeration A → A → Enumeration A
  | xs, a => append xs (.cons a .nil)

end Enumeration


/--
Definition 3: Decoding Map
-/
structure DecodingMap (X : Type v) where
  ζ : Nat → Option X







end Measurement
