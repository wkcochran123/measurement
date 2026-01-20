import Std

namespace Measurement

/--
Definition 1: Enumeration Map.
-/
class EnumerationMap (S : Type u) (X : Type v) where
  index : S -> X -> Nat

/--
Definition 2: Symbol Map.
-/
abbrev SymbolMap (X : Type u) : Type u :=
  Nat -> Option X

/--
Axiom 1 : Enumeration.
-/
inductive Enumeration (X : Type u) : Type u
  | nil  : Enumeration X
  | cons : X -> Enumeration X -> Enumeration X

end Measurement
