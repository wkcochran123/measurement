/-
Measurement/Chapter1/Propositions.lean

Chapter 1, Proposition 1:
There exists a trivial enumeration using the symbol map Nat -> Nat.
-/

import Measurement.Chapter1.Axioms

namespace Measurement

universe u v


/--
Proposition 1: There exists an enumeration of the natural numbers.
-/
def trivialEnumeration : EnumerationMap Nat :=
{ η := fun n => n
, surjective := by
    intro n
    exact ⟨n, rfl⟩
}

theorem exists_trivial_enumeration : Nonempty (EnumerationMap Nat) :=
  ⟨trivialEnumeration⟩


def ledgerOfNaturalNumbers: Ledger Nat :=
  { head := 1
  , tail :=
      let rec aux (n : Nat) : Enumeration Nat :=
        match n with
        | 0     => .nil
        | n + 1 => .cons n (aux n)
      aux  (Nat.succ 0)
  }

/--
Proposition 2: There exists a ledger of the natural numbers.
-/
theorem exists_ledgerOfNaturalNumbers : ∃ L : Ledger Nat, True :=
by
  exact ⟨ledgerOfNaturalNumbers, trivial⟩



end Measurement
