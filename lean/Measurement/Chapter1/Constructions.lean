/-
Measurement/Chapter1/Constructions.lean

Constructions layer (Chapter 1): Lisp operations on Enumeration,
and the concrete nonempty spine TimeSeries := [head, tail].

Depends on Chapter1/ZFC.lean.
-/

import Measurement.Chapter1.ZFC


namespace Measurement

/--
TimeSeries interface: something you can call `first`, `last`, `index`, etc. on.

We keep it minimal: nonempty by construction (via `first : X`).
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
