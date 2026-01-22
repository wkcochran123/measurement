import Measurement.Chapter1.Definitions

namespace Measurement

universe u v
/-
Axiom 1 : The Axiom of Peano.

We can define a hypothetical label for an object and assign those
labels to numbers.
-/


/-- Definition 1: Enumeration Map.

A map from X to Nat together with surjectivity.
-/

structure EnumerationMap (X : Type u) where
  η : X → Nat
  surjective : Function.Surjective η


end Measurement
