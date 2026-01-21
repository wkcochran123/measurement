import Std

import Measurement.Chapter1.Propositions

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Basic


namespace Measurement
namespace ZFC

universe u

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
/-- A useful set to define:  the real numbers (t,t+1] -/
def unitIocAt (t : Real) : Set Real :=
  let a : Real := ((Real.instArchimedean.floorRing.floor t : Int) : Real)
  Set.Ioc a (a + 1)


/-- A ZFC-style finite set wrapper. -/
structure FiniteSet (α : Type u) where
  carrier : Finset α

/-- The empty finite set. -/
def empty {α : Type u} : FiniteSet α :=
{ carrier := ∅ }


end ZFC
end Measurement
