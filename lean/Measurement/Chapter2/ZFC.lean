import Std

import Measurement.Chapter1.Propositions

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Basic


namespace Measurement
namespace ZFC

universe u

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
