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
def restrict {α β : Type} (s : Set α) (f : α -> β) :
  {x : α // x ∈ s} -> β :=
  fun x => f x.1


/-- The positive rational numbers. -/
def Qpos : Type :=
  { q : Rat // 0 < q }

/-- The positive real numbers. -/
def Rpos : Type :=
  { r : Real // 0 < r }

end ZFC
end Measurement
