import Std

import Measurement.Chapter1.Propositions

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Basic


namespace Measurement
namespace ZFC

universe u


/--
  Abbreviation for the rational and positive rational numbers.
-/
abbrev QPos := { q : Rat // 0 < q }
abbrev Q := Rat

/--
  Unit interval of the form (a, a+1] around a real number t.
-/
def unitIocAt (t : Real) : Set Real :=
  let a : Real := ((Real.instArchimedean.floorRing.floor t : Int) : Real)
  Set.Ioc a (a + 1)



end ZFC
end Measurement
