/-
Measurement/Chapter1/Constructions.lean

Constructions layer (Chapter 1): Lisp operations on Enumeration,
and the concrete nonempty spine TimeSeries := [head, tail].

-/

import Measurement.Chapter1.Axioms


namespace Measurement

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

inductive Prefix {A : Type u} : Enumeration A -> Enumeration A -> Prop
  | nil  (t) : Prefix .nil t
  | cons (a) (s t) : Prefix s t -> Prefix (.cons a s) (.cons a t)

variable {A : Type u}

/-- Append a single element to the end of an enumeration. -/
def snoc : Enumeration A → A → Enumeration A
  | xs, a => append xs (.cons a .nil)

end Enumeration


/--
Definition 4: Decoding Map
-/
structure DecodingMap (X : Type v) where
  ζ : Nat → Option X

/-- A partial order on a carrier. -/
structure PartialOrder (C : Type u) where
  le        : C -> C -> Prop
  refl      : forall a, le a a
  antisymm  : forall a b, le a b -> le b a -> a = b
  trans     : forall a b c, le a b -> le b c -> le a c


/--
A bucket structure is a Nat-indexed multimap enumeration of C,
together with an internal comparison for sorting within each fiber.
-/
structure Bucket (C : Type u) where
  enum : C -> Nat                     -- the "level" / index (multi-map allowed)
  fib  : Nat -> List C          -- the bucket at index n (List/Finset/etc)
  le  : C -> C -> Prop               -- internal bucket sort (tie-breaker)


/--
A poset in this framework is a carrier equipped with:
  1) a global partial order, and
  2) an enumeration bucket structure.

Compatibility is assumed: the global order agrees with the induced
lexicographic order (enum first, then leᵇ within fibers).
-/
structure Poset (C: Type u) where
  po      : PartialOrder C
  bucket  : Bucket C

  -- assumed law (not implemented):
  -- po.le a b  <->  bucket.enum a < bucket.enum b
  --           or (bucket.enum a = bucket.enum b ∧ bucket.leᵇ a b)

/--
Definition: Time Series.

A time series is a finite or countably infinite sequence of records
that is strictly ordered by a partial order, with no repeated positions.
-/
structure TimeSeries (E : Type u)(X : Type v) where
  data : E → X
  order : PartialOrder E
  /-- The sequence of records (partial to allow finite series). -/
  seq : Nat → Option E
  /-- No two distinct records share the same position. -/
  seq_injective :
    ∀ {n m r},
      seq n = some r →
      seq m = some r →
      n = m
  /-- Successive records respect the order. -/
  seq_ordered :
    ∀ {n r s},
      seq n = some r →
      seq (n+1) = some s →
      order.le r s





end Measurement
