/-
Measurement/Chapter1/Constructions.lean

Constructions layer (Chapter 1): Lisp operations on Enumeration,
and the concrete nonempty spine TimeSeries := [head, tail].

Depends on Chapter1/ZFC.lean.
-/

import Measurement.Chapter1.Axioms


namespace Measurement

/--
Definition 2: Symbol Map.
-/
abbrev SymbolMap (X : Type u) : Type u :=
  Nat -> Option X

/--
Definition 3: Time Series
-/
structure TimeSeries (X : Type u) : Type u where
  first : X
  rest  : Nat -> Option X

  /-- 0-indexed: 0 = first, n+1 = rest n. -/
  index : Nat -> Option X :=
    fun n =>
      match n with
      | 0     => some first
      | n + 1 => rest n

end Measurement
