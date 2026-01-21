/-
Measurement/Chapter1/Propositions.lean

Chapter 1, Proposition 1:
There exists a trivial enumeration using the symbol map Nat -> Nat.
-/

import Measurement.Chapter1.Definitions

namespace Measurement

universe u v


/--
Proposition 1 (Chapter 1): there exists a trivial enumeration.

We package it as `Nonempty` so it is easy to use downstream.
-/

def trivialEnumeration: EnumerationMap Nat :=
  fun n => n

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

  /-- There exists a ledger of natural numbers. -/
theorem exists_ledgerOfNaturalNumbers : ∃ L : Ledger Nat, True :=
by
  exact ⟨ledgerOfNaturalNumbers, trivial⟩



end Measurement
