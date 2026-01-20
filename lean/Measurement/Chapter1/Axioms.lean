import Measurement.Chapter1.ZFC

/-
Axiom 1 : The Axiom of Peano.

We can define a hypothetical label for an object and assign those
labels to numbers.
-/

/--
Definition 1: Symbol Map.
-/
abbrev SymbolMap (X : Type u) : Type u :=
  Nat -> Option X


/-
Defintion 2: Enumeration.
-/
inductive Enumerable (A : Type u) : Type u
  | nil : Enumerable A
  | cons : A → Enumerable A → Enumerable A
