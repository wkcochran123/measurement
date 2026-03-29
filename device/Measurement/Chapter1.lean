/-
Measurement
Chapter 2:
-/

namespace Measurement
universe i

structure Fact where
  truth : Prop
  decTruth : Decidable truth

namespace Fact
def Truth : Prop := True
end Fact


-- Big Endian Binary number with LE ordering.
inductive Number where
  | zero : Number
  | succ : Fact → Number → Number

namespace Number
def le : Number → Number → Prop
  | .zero, _ => True
  | .succ _ _, .zero => False
  | .succ p1 n1', .succ p2 n2' =>
      match p1.decTruth, p2.decTruth with
      | isTrue _,  isTrue _  => le n1' n2'
      | isTrue _,  isFalse _ => False
      | isFalse _, isTrue _  => True
      | isFalse _, isFalse _ => le n1' n2'
end Number

-- And the notation to match.
instance : LE Number where
  le := Number.le

structure Carrier
    (carrier: Fact)
  where
  present? : Option Number → Prop := fun s =>
    match s with
    | none      => False
    | some f  => match f with
      | .zero => carrier.truth
      | .succ p _ => p.truth


class DISTINGUISHABLE
    (Carrier: Number)
    (Label: Type 1)
    [DecidableEq Label]
    where

  different? : Label → Label → Prop :=
    fun s1 s2 => s1 ≠ s2
  distinct? : Label → Prop :=
    fun s => ∃ c : Label, different? s c
  dec_distinct : DecidablePred distinct?

inductive Naturals
    (Value: Number)
    (NaturalNumber: Type 1)
    [DecidableEq NaturalNumber]
    [DISTINGUISHABLE Value NaturalNumber]
  where
  | value : Fact → Number → Naturals Value NaturalNumber
  | number : Fact → Number → NaturalNumber → Naturals Value NaturalNumber

structure Ordering
    (Value: Number)
    (NaturalNumber: Type 1)
    [DecidableEq NaturalNumber]
    [DISTINGUISHABLE Value NaturalNumber]
  where
  value: Number
  number: Type 1

  le? : Type 1 → Type 1 → Prop

namespace Ordering
variable  {Value: Number}
          {NaturalNumber: Type 1}
          [DecidableEq NaturalNumber]
          [DISTINGUISHABLE Value NaturalNumber]
          {v : Ordering Value NaturalNumber}
def le : Type 1 → Type 1 → Prop := fun a b =>
  v.le? a b
end Ordering


class ADMISSIBLE
  (Signal: Number)
  (Threshold: Type 1)
  (Invariant: Type i)
  [DecidableEq Invariant]
  [DecidableEq Threshold]
  [DecidableEq Number]
  [DISTINGUISHABLE Signal Threshold]
  where

  admissible? : Number → Number → Prop := fun stimulus threshold =>
    ∃ h : Ordering Signal Threshold, stimulus ≤ h.value ∧ h.value ≤ threshold


inductive IndexedVariable
    (Value: Number)
    (NaturalNumber: Type 1)
    (Object: Type i)
    [DecidableEq Number]
    [DecidableEq NaturalNumber]
    [DecidableEq Object]
    [DISTINGUISHABLE Value NaturalNumber]
    [ADMISSIBLE Value NaturalNumber Object]
  where
  | value : Number → NaturalNumber → IndexedVariable Value NaturalNumber Object
  | encoding : Number → NaturalNumber → Object → IndexedVariable Value NaturalNumber Object


structure Variable
    (PhysicalValue: Number)       -- This is the reading of the instrument
    (MetaphysicalValue: Type 1)   -- This is the ℝeal number the physical value is supposed to be representing.
    (RationalRepresentation: Type i)    -- This is a rational approximation of the MetaphysicalValue, which we
                                        -- can use for calculations.
    [DecidableEq Number]
    [DecidableEq MetaphysicalValue]
    [DecidableEq RationalRepresentation]
    [DISTINGUISHABLE PhysicalValue MetaphysicalValue]
    [ADMISSIBLE PhysicalValue MetaphysicalValue RationalRepresentation]

  where
  observation : Number
  rational : Type i
  real : Type 1

inductive Sequence
    (Representation: Number)
    (RunningValue: Type 1)
    (StepValue: Type i)
    [DecidableEq Number]
    [DecidableEq Column]
    [DecidableEq Row]
    [DISTINGUISHABLE Representation Column]
    [ADMISSIBLE Representation Column Row]
  where
  | value : Number → NaturalNumber → Sequence Representation RunningValue StepValue
  | encoding : Number → NaturalNumber → Object → Sequence Representation RunningValue StepValue


namespace RationalNumber
variable  {Value: Number}
          {Numerator: Type 1}
          {Denominator: Type 1}
          [DecidableEq Number]
          [DecidableEq Numerator]
          [DecidableEq Denominator]
          [DISTINGUISHABLE Value Numerator]
          [DISTINGUISHABLE Value Denominator]
          [ADMISSIBLE Value Numerator Denominator] -- Keep an eye out for infinity
          {order: Ordering Value Numerator}
          (R: RationalNumber Value Numerator Denominator order)

def lt? : Type 1 → Type 1 → Prop := fun a b =>
  R.le? a b ∧ ¬ R.le? b a
end RationalNumber

class COUNTABLE
    (Value: Number)
    (Representation: Type 1)
    (Accumulation: Type i)
    [ADMISSIBLE Value Representation Accumulation]



inductive Decomposition
    (Value: Number)
    (Numerator: Type 1)
    (Denominator: Type 1)
    (Pieces: Type 1 × Type 1)
    [DecidableEq Number]
    [DecidableEq Numerator]
    [DecidableEq Denominator]
    [DISTINGUISHABLE Value Numerator]
    [DISTINGUISHABLE Value Denominator]
    [ADMISSIBLE Value Numerator Denominator] -- Keep an eye out for infinity
    (Order: Ordering Value Numerator)
    (Rational: RationalNumber Value Numerator Denominator Order)
    (Countable: COUNTABLE Value Numerator Denominator Accumulation Order Rational)
  where
  | zero :  (Type 1) × (Type 1) →
            Decomposition Value Numerator Denominator Pieces Order Rational Countable
  | succ :  (Type 1) × (Type 1) →
            (Type 1) → (Type 1) →
            Decomposition Value Numerator Denominator Pieces Order Rational Countable →
            Decomposition Value Numerator Denominator Pieces Order Rational Countable

structure Bisection
    (Value: Number)
    (Numerator: Type 1)
    (Denominator: Type 1)
    (Pieces: (Type 1) × (Type 1))
    [DecidableEq Number]
    [DecidableEq Numerator]
    [DecidableEq Denominator]
    [DISTINGUISHABLE Value Numerator]
    [DISTINGUISHABLE Value Denominator]
    [ADMISSIBLE Value Numerator Denominator] -- Keep an eye out for infinity
    (Order: Ordering Value Numerator)
    (Rational: RationalNumber Value Numerator Denominator Order)
  where


structure Sequence
    (Value: Number)
    (Numerator: Type 1)
    (Denominator: Type 1)
    (Accumulation: Type i)
    [DecidableEq Number]
    [DecidableEq Numerator]
    [DecidableEq Denominator]
    [DecidableEq Accumulation]
    [DISTINGUISHABLE Value Numerator]
    [DISTINGUISHABLE Value Denominator]
    [ADMISSIBLE Value Numerator Denominator] -- Keep an eye out for infinity
    (Order: Ordering Value Numerator)
    (Rational: RationalNumber Value Numerator Denominator Order)
    (Countable: COUNTABLE Value Numerator Denominator Accumulation Order Rational)
  where

  zero : Type
  count: COUNTABLE Value Numerator Denominator Accumulation Order Rational
  value : Type i

  converged? : Type 1 → Type 1 → Prop := fun residue threshold =>
    Countable.lt? residue threshold

inductive Iteration
    (Value: Number)
    (Numerator: Type 1)
    (Denominator: Type 1)
    (Accumulation: Type i)
    [DecidableEq Number]
    [DecidableEq Numerator]
    [DecidableEq Denominator]
    [DecidableEq Accumulation]
    [DISTINGUISHABLE Value Numerator]
    [DISTINGUISHABLE Value Denominator]
    [ADMISSIBLE Value Numerator Denominator] -- Keep an eye out for infinity
    (Order: Ordering Value Numerator)
    (Rational: RationalNumber Value Numerator Denominator Order)
    (Countable: COUNTABLE Value Numerator Denominator Accumulation Order Rational)
    (sequence: Sequence Value Numerator Denominator Accumulation Order Rational Countable)
    where
  | zero :  (Sequence Value Numerator Denominator Accumulation Order Rational Countable) →
            Iteration Value Numerator Denominator Accumulation Order Rational Countable sequence
  | succ :  Fact →
            (Sequence Value Numerator Denominator Accumulation Order Rational Countable) →
            Iteration Value Numerator Denominator Accumulation Order Rational Countable sequence →
            Iteration Value Numerator Denominator Accumulation Order Rational Countable sequence
