import Measurement.Chapter1.ZFC

/--
Axiom 1 : The Axiom of Peano.
-/
inductive Enumeration (X : Type u) : Type u
  | nil  : Enumeration X
  | cons : X -> Enumeration X -> Enumeration X
