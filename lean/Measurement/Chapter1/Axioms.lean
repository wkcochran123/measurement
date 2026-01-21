import Measurement.Chapter1.ZFC

/-
Axiom 1 : The Axiom of Peano.

We can define a hypothetical label for an object and assign those
labels to numbers.
-/

/--
Definition 1: Enumerable Map.

Surjective
-/
abbrev EnumerationMap (X : Type u) : Type u :=
  X -> Nat
