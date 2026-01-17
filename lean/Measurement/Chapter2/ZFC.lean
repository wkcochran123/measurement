import Std

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic

namespace Measurement
namespace ZFC

/-- A useful set to define:  the real numbers (t,t+1] -/
def unitIocAt (t : Real) : Set Real :=
  let a : Real := ((Real.floor t : Int) : Real)
  Set.Ioc a (a + 1)


/-- The floor function -/
def floorNat (x : Real) : Nat :=
  Int.toNat (Real.floor x)

-- restrict a function to a set
def restrict {α β : Type} (s : Set α) (f : α -> β) :
  {x : α // x ∈ s} -> β :=
  fun x => f x.1


end ZFC
end Measurement
