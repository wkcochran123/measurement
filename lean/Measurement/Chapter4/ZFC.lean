import Std

import Measurement.Chapter2.Propositions

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Basic



namespace Measurement
namespace ZFC

universe u

/-- The floor function

This is the crack in math that allows us to see the
continuum.  This is the implementation of temporal
friction -/
noncomputable def floorNat (x : Real) : Nat :=
  Int.toNat (Real.instArchimedean.floorRing.floor x)


-- restrict a function to a set
/--
  A partial order on a type C.
-/
structure PartialOrder (C : Type u) where
  le        : C -> C -> Prop
  refl      : forall a, le a a
  antisymm  : forall a b, le a b -> le b a -> a = b
  trans     : forall a b c, le a b -> le b c -> le a c

structure Poset (C : Type u) where
  po : PartialOrder C

  Bucket : Type u
  enum   : Bucket -> C -> Nat
  fib    : Bucket -> Nat -> List C
  leB    : Bucket -> C -> C -> Prop

  buckets : Enumeration Bucket

nd ZFC
end Measurement
