import Std

import Measurement.Chapter1.Constructions

namespace Measurement

universe u v w


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
Ledger: concrete nonempty spine [head, tail...].
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
  | .nil => { head := L.head, tail := .nil }  -- unreachable; keeps total
  | .cons h t => { head := h, tail := t }

def size (L : Ledger X) : Nat :=
  Enumeration.len (L.toEnum)

end Ledger

/--
Ledger implements the TimeSeries interface.
-/
def Ledger.asTimeSeries {X : Type u} (L : Ledger X) : TimeSeries X :=
{ first := L.head
, rest  := fun n => Enumeration.nth L.tail n
}

end Measurement
