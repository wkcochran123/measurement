import Std

import Measurement.Chapter1.Constructions

namespace Measurement

universe u v w



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

end Measurement
