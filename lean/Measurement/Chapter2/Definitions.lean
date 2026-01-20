import Std


import Measurement.Chapter1.Definitions
import Measurement.Chapter2.Constructions

namespace Measurement

namespace Enumeration
/-- Find the first index of `a` in the enumeration, if present. -/
def find [DecidableEq α] : Enumeration α -> α -> Option Nat
  | .nil,        _ => none
  | .cons b t, a =>
      if b = a then
        some 0
      else
        match find t a with
        | some n => some (n + 1)
        | none   => none

def get : Enumeration α -> Nat -> Option α
  | .nil,      _     => none
  | .cons a _, 0     => some a
  | .cons _ t, n + 1 => get t n
end Enumeration

/-- Definition: Alphabet -/
structure Alphabet (σ : Type v) where
  symbols : Enumeration σ

namespace Alphabet

def get (A : Alphabet σ) : Nat -> Option σ :=
  fun n => Enumeration.get A.symbols n

def index [DecidableEq σ] (A : Alphabet σ) : σ -> Option Nat :=
  fun s => Enumeration.find A.symbols s

end Alphabet

/-- Definition 5: Refinement -/
structure Refinement (X : Type u) where
  refine : X -> Enumeration X -> Enumeration X

/-- Definition 6: Structure -/
structure Record (σ : Type v) where
  i : Nat
  σ : σ
  k : Nat


/-- Definition 7: Moment -/
abbrev Moment (t : Real) : Type :=
  { u : Real // u ∈ ZFC.unitIocAt t } -> Real


/-- Definition 8: Representational Map -/
class Representation (σ : Type u) (X : Type v) where
  encode : X -> σ
  decode : σ -> X


/-- Definition 9: Predition Map -/
class Prediction (X : Type u) (Y : Type v) where
  predict : X -> Y


/-- Definition 10: Event -/
structure Event (S : Type u)(A: Alphabet σ) where
  records : ZFC.FiniteSet (Record σ)


/-- Definition 11: Phenomenon -/
structure Phenomenon (S: Type u)(σ: Alphabet A) where
  events : ZFC.FiniteSet (Event u σ)

structure Instrument (S : Type u) where
  Sigma: Alphabet S
  phenomenon: Phenomenon (S:=S) Sigma

abbrev Clock := Instrument Nat

end Measurement
