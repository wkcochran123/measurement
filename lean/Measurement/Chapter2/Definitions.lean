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
/--
Definition: Time Series.

A time series is a finite or countably infinite sequence of records
that is strictly ordered by a partial order, with no repeated positions.
-/
structure TimeSeries (E : Type u)(X : Type v) where
  data : E → X
  order : PartialOrder E
  /-- The sequence of records (partial to allow finite series). -/
  seq : Nat → Option E
  /-- No two distinct records share the same position. -/
  seq_injective :
    ∀ {n m r},
      seq n = some r →
      seq m = some r →
      n = m
  /-- Successive records respect the order. -/
  seq_ordered :
    ∀ {n r s},
      seq n = some r →
      seq (n+1) = some s →
      order.le r s

end Measurement
