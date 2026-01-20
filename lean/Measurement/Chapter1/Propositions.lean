/-
Measurement/Chapter1/Propositions.lean

Chapter 1, Proposition 1:
There exists a trivial enumeration using the symbol map Nat -> Nat.
-/

import Measurement.Chapter1.Definitions

namespace Measurement

universe u v

/-- The trivial Nat enumeration: symbols are just naturals (identity). -/
def trivialNatEnumeration : Enumerable Unit Nat :=
{ eta := fun _ n => n
, rho := fun _ n => some n
, rho_eta := by
    intro s x
    rfl
}

/--
Proposition 1 (Chapter 1): there exists a trivial enumeration.

We package it as `Nonempty` so it is easy to use downstream.
-/
theorem exists_trivial_enumeration : Nonempty (Enumerable Unit Nat) :=
  ⟨trivialNatEnumeration⟩

end Measurement
