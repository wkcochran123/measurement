/-
Measurement/Chapter1/Constructions.lean

Constructions layer (Chapter 1): Lisp operations on Enumeration,
and the concrete nonempty spine TimeSeries := [head, tail].

-/

import Measurement.Chapter1.Axioms


namespace Measurement

/--
Definition 3: Enumerable
-/
structure Enumerable (S : Type u) (X : Type v) where
  eta : S → X → Nat
  rho : S → Nat → Option X
  rho_eta : ∀ (s : S) (x : X), rho s (eta s x) = some x

/--
Definition 3: Enumeration
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

end Enumeration



/--
Definition 3: Time Series
-/
structure TimeSeries (X : Type u) : Type u where
  first : X
  rest  : Nat -> Option X

  /-- 0-indexed: 0 = first, n+1 = rest n. -/
  index : Nat -> Option X :=
    fun n =>
      match n with
      | 0     => some first
      | n + 1 => rest n

end Measurement
