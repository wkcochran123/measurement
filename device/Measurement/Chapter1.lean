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
def Truth : Fact := { truth := true, decTruth := Decidable.isTrue rfl }
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
    (Observation: Fact)
    (Symbol: Type 1)
    [DecidableEq Symbol]
    where

  fact: Fact
  symbol: Type Symbol

  distinct? : Prop := True
  different? : Type Symbol → Prop :=
    fun s1 => s1 ≠ symbol

  dec_distinct : DecidablePred different?


inductive Natural
  where
  | zero : Fact → Number → Natural
  | number : Fact → Number → Natural → Natural

namespace Natural
def le : Natural → Natural → Prop
  | .zero _ _ , _  => True
  | .number _ _ _ , .zero _ _ => False
  | .number p1 n1' _, .number p2 n2' _ =>
    p1.truth /\ p2.truth /\ n1' ≤ n2'
end Natural

instance : LE Natural where
  le := Natural.le

structure CountingProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
  where
  sent? : Prop := Observation.truth
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  received? : Prop := sent? ∧ transport_carrier.present? (some .zero)
  count: Natural → Natural := fun n =>
    match n with
    | .zero _ _ => .zero observation .zero
    | .number _ _ _ => .number observation value index


class ADMISSIBLE
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    where
  admission_process  : CountingProcess Observation Symbol η transport_carrier
  admissible? : Number → Number → Prop := fun stimulus threshold =>
    stimulus ≤ admission_process.value ∧ admission_process.value ≤ threshold


inductive Rational
  where
  | zero : Fact → Number → Natural → Rational
  | number : Fact → Number → Natural → Rational → Rational


namespace Rational
def le : Rational → Rational → Prop
  | .zero _ _ _ , _  => True
  | .number _ _ _ _ , .zero _ _ _ => False
  | .number p1 n1' _ _, .number p2 n2' _ _ =>
    p1.truth /\ p2.truth /\ n1' ≤ n2'       -- We assume the rationals are sorted.
end Rational

instance : LE Rational where
  le := Rational.le

structure IndexingProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ψ: Number)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
  where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  bound: Rational

  observed? : Prop := match η with
    | .zero _ _ => True
    | .number f num _ => f.truth /\ ψ ≤ num


  lt? : Rational → Rational → Prop := fun r s =>
    r ≤ s ∧ ¬ s ≤ r

  ζ?: Natural → Number := fun n =>
    match n with
    | .zero _ _ => ψ
    | .number f num _ => match f.decTruth with
      | isTrue _ => ψ
      | isFalse _ => num


class COUNTABLE
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ψ: Number)
    (φ: Rational)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    where
  index: IndexingProcess Observation Symbol η ψ transport_carrier
  counted? : Prop := index.lt? φ index.bound


inductive Sequence
  |nil: Fact → Number → Natural → Rational → Fact → Sequence
  |index :  Fact → Number → Natural → Rational → Fact → Sequence → Sequence

structure LimitProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [count: COUNTABLE Observation Symbol η ζ φ transport_carrier]
    where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  rational: Rational
  sequence: Sequence

  convergent? : Rational → Prop := fun s => count.counted? ∨ s ≤ φ
  count? : Sequence → Sequence := fun s1 =>
    match s1 with
    | .nil a b c d e => Sequence.nil a b c d e
    | .index _ _ _ _ _ _ => match count.counted? with
      | _ => s1


class CORRELANT
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
  where
  cauchy_process: LimitProcess Observation Symbol η ζ φ transport_carrier
  correllant? : Rational → Prop := fun s => cauchy_process.convergent? s


inductive Limit
  |nil: Fact → Number → Natural → Rational → Sequence → Limit
  |index :  Fact → Number → Natural → Rational → Sequence → Limit → Limit

structure CauchyProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [correlant: CORRELANT Observation Symbol η ζ φ transport_carrier]
    where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  rational: Rational
  sequence: Sequence
  point: Limit

  converged?: Prop := correlant.correllant? rational
  iterate: Limit → Limit := fun l1 =>
    match l1 with
    | .nil a b c d e => Limit.nil a b c d e
    | .index _ _ _ _ _ l2 => Limit.index observation value index rational correlant.cauchy_process.sequence l2

class REAL
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ transport_carrier]
  where
  dτ: CauchyProcess Observation Symbol η ζ φ ψ transport_carrier
  real? : dτ.converged?


inductive Invariant
  where
  |initial_condition: Fact → Number → Natural → Rational → Sequence → Limit → Invariant
  |invariant: Fact → Number → Natural → Rational → Sequence → Limit → Fact → Invariant → Invariant

structure Variable
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    (x: Invariant)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ transport_carrier]
    [REAL Observation Symbol η ζ φ ψ transport_carrier]
  where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  rational: Rational
  sequence: Sequence
  point: Limit
  unit: Invariant

  different? : Type Symbol → Prop :=
    fun s1 => s1 ≠ symbol
  dec_distinguished : DecidablePred different?
  fact: Fact

  evolve? : Invariant → Invariant := fun i1 =>
    match i1 with
    | .initial_condition a b c d e f => Invariant.initial_condition a b c d e f
    | .invariant _ _ _ _ _ _ g i2 => Invariant.invariant observation value index rational sequence point g i2


class COMPUTABLE
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    (x: Invariant)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ transport_carrier]
    [REAL Observation Symbol η ζ φ ψ transport_carrier]
  where
  x_t: Variable Observation Symbol η ζ φ ψ x transport_carrier
  fact? : Fact := Fact.mk x_t.fact.truth x_t.fact.decTruth

inductive Computation
  where
  |input: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation
  |computation: Fact → Number → Natural → Rational → Sequence → Limit → Invariant →   -- Input
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant →   -- Output
                Computation → Computation

structure TuringProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ transport_carrier]
    [REAL Observation Symbol η ζ φ ψ transport_carrier]
    [COMPUTABLE Observation Symbol η ζ φ ψ x transport_carrier]
    where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  rational: Rational
  sequence: Sequence
  point: Limit
  unit: Invariant
  magnitude: Computation

  compute?: Computation → Computation := fun c1 =>
    match c1 with
    | .input _ _ _ _ _ _ _ => Computation.input observation value index rational sequence point unit
    | .computation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => magnitude


class NOISY
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ transport_carrier]
    [real: REAL Output Symbol η ζ φ ψ transport_carrier]
    [input: COMPUTABLE Output Symbol η ζ φ ψ x transport_carrier]
    where
  noise_process: TuringProcess Output Symbol η ζ φ ψ x f transport_carrier
  rounded? : Fact := input.fact?


inductive State
  where
  |computation: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →   -- Program
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →   -- Input
                Fact → State
  |refinement:  Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →  -- State
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →  -- Output
                Fact → State → State


structure AdmissionProcess
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ transport_carrier]
    [REAL Output Symbol η ζ φ ψ transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ ψ x transport_carrier]
    [noise: NOISY Output Symbol η ζ φ ψ x f transport_carrier]
  where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  rational: Rational
  sequence: Sequence
  point: Limit
  unit: Invariant
  magnitude: Computation
  state: State


  observed? : State → State := fun s1 =>
    match s1 with
    | .computation a b c d e f g h i j k l m n o p _  => State.computation a b c d e f g h i j k l m n o p (noise.rounded?)
    | .refinement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
           State.refinement
              noise.noise_process.observation
              noise.noise_process.value
              noise.noise_process.index
              noise.noise_process.rational
              noise.noise_process.sequence
              noise.noise_process.point
              noise.noise_process.unit
              noise.noise_process.magnitude
              observation
              value
              index
              rational
              sequence
              point
              unit
              magnitude
              noise.rounded?
              state


class LAWFUL
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ transport_carrier]
    [REAL Output Symbol η ζ φ ψ transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ ψ x f transport_carrier]
  where
  admission_process: AdmissionProcess Output Symbol η ζ φ ψ x f m transport_carrier
  admissible? : State → State → Prop := fun t1 t2 => admission_process.observed? t1 = t2

inductive Ledger
  where
  |alphabet: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →    -- Program
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →    -- Input
                Fact → Ledger
  |readings:  Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →  -- State
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →    -- Output
                Fact → Ledger → Ledger



structure Instrument
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ transport_carrier]
    [REAL Output Symbol η ζ φ ψ transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ ψ x f transport_carrier]
    [law: LAWFUL Output Symbol η ζ φ ψ x f m transport_carrier]
  where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  rational: Rational
  sequence: Sequence
  point: Limit
  unit: Invariant
  magnitude: Computation
  state: State
  ledger: Ledger

  refinement: Ledger → Ledger := fun l1 =>
    match l1 with
    | .alphabet a b c d e f g h i j k l m n o p q r s => Ledger.alphabet a b c d e f g h i j k l m n o p q r s
    | .readings _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  =>
        Ledger.readings
          law.admission_process.observation
          law.admission_process.value
          law.admission_process.index
          law.admission_process.rational
          law.admission_process.sequence
          law.admission_process.point
          law.admission_process.unit
          law.admission_process.magnitude
          law.admission_process.state
          observation
          value
          index
          rational
          sequence
          point
          unit
          magnitude
          state
          Fact.Truth
          ledger


end Measurement
