/-
Measurement
Chapter 2:
-/

namespace Measurement
universe i

class Fact where
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
  admissible? : Rational → Rational → Prop := fun stimulus threshold =>
    stimulus ≤ index.bound ∧ index.bound ≤ threshold


inductive Sequence
  |nil: Fact → Number → Natural → Rational → Fact → Sequence
  |index :  Fact → Number → Natural → Rational → Fact → Sequence → Sequence

namespace Sequence
def le: Sequence → Sequence → Prop
  | .nil _ _ _ _ _, _ => True
  | .index _ _ _ _ _ _, .nil _ _ _ _ _ => False
  | .index p1 n1 i1 r1 f1 s1, .index p2 n2 i2 r2 f2 s2 =>
    p1.truth /\ p2.truth /\ n1 ≤ n2 /\ i1 ≤ i2 /\ r1 ≤ r2 /\ f1.truth /\ f2.truth /\ le s1 s2
end Sequence

instance : LE Sequence where
  le := Sequence.le

structure LimitProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
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

  bounded? : Sequence → Prop := fun s => count.counted? ∨ s ≤ s
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
    (s: Sequence)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [count: COUNTABLE Observation Symbol η ζ φ transport_carrier]
  where
  limit_process: LimitProcess Observation Symbol η ζ φ s transport_carrier
  admissible?: Sequence → Sequence → Prop := fun s1 s2 =>
        limit_process.bounded? s1 ∧
        limit_process.bounded? s2 ∧
        s1 ≤ s2 ∧ s2 ≤ s1  -- Equivalent ordering, these guys can be ordered, but need not be.

inductive Limit
  |nil: Fact → Number → Natural → Rational → Sequence → Limit
  |index :  Fact → Number → Natural → Rational → Sequence → Limit → Limit

namespace Limit
def le: Limit → Limit → Prop
  | .nil _ _ _ _ _, _ => True
  | .index _ _ _ _ _ _, .nil _ _ _ _ _ => False
  | .index p1 n1 i1 r1 s1 l1, .index p2 n2 i2 r2 s2 l2 =>
    p1.truth /\ p2.truth /\ n1 ≤ n2 /\ i1 ≤ i2 /\ r1 ≤ r2 /\ s1 ≤ s2 /\ le l1 l2
end Limit

instance : LE Limit where
  le := Limit.le

structure CauchyProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [correlant: CORRELANT Observation Symbol η ζ φ s transport_carrier]
    where
  symbol: Type Symbol
  observation: Fact
  value: Number
  index: Natural
  rational: Rational
  sequence: Sequence
  point: Limit

  convergent? : Prop := correlant.limit_process.bounded? sequence
  iterate: Limit → Limit := fun l1 =>
    match l1 with
    | .nil a b c d e => Limit.nil a b c d e
    | .index _ _ _ _ _ l2 => Limit.index observation value index rational correlant.limit_process.sequence l2

class REAL
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ s transport_carrier]
  where
  dτ: CauchyProcess Observation Symbol η ζ φ s ψ transport_carrier
  admissible?: Limit → Limit → Prop := fun l1 l2 => dτ.convergent? ∧ l1 ≤ l2 ∧ ¬ l2 ≤ l1  -- Strict ordering! Reals are totally ordered.


inductive Invariant
  where
  |initial_condition: Fact → Number → Natural → Rational → Sequence → Limit → Invariant
  |invariant: Fact → Number → Natural → Rational → Sequence → Limit → Fact → Invariant → Invariant

namespace Invariant
def le: Invariant → Invariant → Prop
  | .initial_condition _ _ _ _ _ _, _ => True
  | .invariant _ _ _ _ _ _ _ _, .initial_condition _ _ _ _ _ _ => False
  | .invariant p1 n1 i1 r1 s1 l1 f1 inv1, .invariant p2 n2 i2 r2 s2 l2 f2 inv2 =>
    p1.truth /\ p2.truth /\ n1 ≤ n2 /\ i1 ≤ i2 /\ r1 ≤ r2 /\ s1 ≤ s2 /\ l1 ≤ l2 /\ f1.truth /\ f2.truth /\ le inv1 inv2
end Invariant

instance : LE Invariant where
  le := Invariant.le

structure Variable
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ s transport_carrier]
    [REAL Observation Symbol η ζ φ s ψ transport_carrier]
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


class RELATABLE
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ s transport_carrier]
    [REAL Observation Symbol η ζ φ s ψ transport_carrier]
  where
  x_t: Variable Observation Symbol η ζ φ s ψ x transport_carrier
  fact? : Fact := Fact.mk x_t.fact.truth x_t.fact.decTruth
  admissible? : Invariant → Invariant → Prop := fun i1 i2 => x_t.evolve? i1 = i2

inductive Computation
  where
  |input: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation
  |computation: Fact → Number → Natural → Rational → Sequence → Limit → Invariant →   -- Input
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant →   -- Output
                Computation → Computation

namespace Computation
def le: Computation → Computation → Prop
  | .input _ _ _ _ _ _ n1, .input _ _ _ _ _ _ n2=> n1 ≤ n2
  | .input _ _ _ _ _ _ n1, .computation _ _ _ _ _ _ _ _ _ _ _ _ _ n2 _ => n1 ≤ n2
  | .computation _ _ _ _ _ _ _ _ _ _ _ _ _ n1 _, .input _ _ _ _ _ _ n2 => n1 ≤ n2
  | .computation _ _ _ _ _ _ _ _ _ _ _ _ _ n1 _, .computation _ _ _ _ _ _ _ _ _ _ _ _ _ n2 _ => n1 ≤ n2
end Computation

instance : LE Computation where
  le := Computation.le

structure TuringProcess
    (Observation: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Observation)
    [DISTINGUISHABLE Observation Symbol]
    [ADMISSIBLE Observation Symbol η transport_carrier]
    [COUNTABLE Observation Symbol η ζ φ transport_carrier]
    [CORRELANT Observation Symbol η ζ φ s transport_carrier]
    [REAL Observation Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Observation Symbol η ζ φ s ψ x transport_carrier]
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
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [real: REAL Output Symbol η ζ φ s ψ transport_carrier]
    [input: RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    where
  noise_process: TuringProcess Output Symbol η ζ φ s ψ x f transport_carrier
  rounded? : Fact := input.fact?
  admissible? : Computation → Computation → Prop := fun c1 c2 =>
    noise_process.compute? c1 = c2


inductive State
  where
  |computation: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →   -- Program
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →   -- Input
                Fact → State
  |refinement:  Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →  -- State
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation →  -- Output
                Fact → State → State

namespace State
def le: State → State → Prop
  | .computation  _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c1
                  _,
    .computation  _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c2
                  _ => c1 ≤ c2
  | .computation  _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c1
                  _,
    .refinement   _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c2
                  _ _ => c1 ≤ c2
  | .refinement  _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c1
                  _ _,
    .refinement   _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c2
                  _ _ => c1 ≤ c2
  | .refinement   _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c1
                  _ _,
    .computation  _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ c2
                  _ => c1 ≤ c2
end State

instance : LE State where
  le := State.le

structure AdmissionProcess
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [noise: NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
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
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
  where
  admission_process: AdmissionProcess Output Symbol η ζ φ s ψ x f m transport_carrier
  admissible? : State → State → Prop := fun t1 t2 => admission_process.observed? t1 = t2

inductive Ledger
  where
  |alphabet: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →    -- Program
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →    -- Input
                Fact → Ledger
  |readings:  Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →  -- State
                Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State →    -- Output
                Fact → Ledger → Ledger

-- The ledger sorts on the internal state, not on program or output.
namespace Ledger
def le: Ledger → Ledger → Prop
  | .alphabet _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ s1
              _,
    .alphabet _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ s2
              _=> s1 ≤ s2
  | .alphabet _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ s1
              _,
    .readings _ _ _ _ _ _ _ _ s2
              _ _ _ _ _ _ _ _ _
              _ _ => s1 ≤ s2
  | .readings _ _ _ _ _ _ _ _ s1
              _ _ _ _ _ _ _ _ _
              _ _,
    .alphabet _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ s2
              _ => s1 ≤ s2
  | .readings _ _ _ _ _ _ _ _ s1
              _ _ _ _ _ _ _ _ _
              _ _,
    .readings _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ s2
              _ _=> s1 ≤ s2
end Ledger

instance : LE Ledger where
  le := Ledger.le

structure MeasurementProcess
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
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
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [law: LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
  where
  symbol: Type Symbol
  response: Type Response
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

  observed? : Prop := observation.truth
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
          Fact.Truth  -- We have managed to store 1 bit in the compiler!  Our whole cloth!
          ledger

class ITERABLE
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
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
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [noisy: NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [law: LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
  where
  measurement_process: MeasurementProcess Output Symbol η ζ φ s ψ x f m l transport_carrier
  admissible?: Ledger → Ledger → Prop := fun l1 l2 => measurement_process.refinement l1 = l2

inductive Tape
  where
  |program: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → Fact → Tape
  |head: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → -- Read head
         Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → -- Write head
         Fact → Tape → Tape

namespace Tape
def le: Tape → Tape → Prop
  | .program _ _ _ _ _ _ _ _ _ _ _,
    .program _ _ _ _ _ _ _ _ _ _ _ => True
  | .program _ _ _ _ _ _ _ _ _ _ _,
    .head _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _
          _ _=> False
  | .head  _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _
          _ _,
    .program _ _ _ _ _ _ _ _ _ _ _=> False
  | .head  _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ l1
          _ _,
    .head  _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ l2
          _ _ => l1 ≤ l2
end Tape

instance : LE Tape where
  le := Tape.le

structure StateChangeProcess
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (Input: Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
  where
  symbol: Type Symbol
  input: Type Input
  response: Type Response
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
  accumulation: Tape

  written? : Prop := observation.truth
  accumulate: Tape → Tape := fun a1 =>
    match a1 with
    | .program a b c d e f g h i j k => Tape.program a b c d e f g h i j k
    | .head    a b c d e f g h i j
               _ _ _ _ _ _ _ _ _ _
               _ m => Tape.head a b c d e f g h i j
                 observation
                 value
                 index
                 rational
                 sequence
                 point
                 unit
                 magnitude
                 state
                 ledger
                 Fact.Truth  -- Another bit!
                 m

class COMPUTABLE
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (Input: Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
  where

  state_change_process: StateChangeProcess Output Symbol η ζ φ s ψ x f m l a Input transport_carrier
  admissible? : Tape → Tape → Prop := fun a1 a2 => state_change_process.accumulate a1 = a2

inductive Automaton
  where
        --  a     b         c           d        e         f      g           h             i        j       k      l
  |state: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → Tape → Fact → Automaton
  |transition: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → Tape →
               Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → Tape →
               Fact → Automaton → Automaton

namespace Automaton
def le: Automaton → Automaton → Prop
  | .state _ _ _ _ _ _ _ _ _ _ k _,
    .state _ _ _ _ _ _ _ _ _ _ l _ => k ≤ l
  | .state _ _ _ _ _ _ _ _ _ _ k _,
    .transition _ _ _ _ _ _ _ _ _ _ _
                _ _ _ _ _ _ _ _ _ _ l
                _ _  => k ≤ l
  | .transition _ _ _ _ _ _ _ _ _ _ _
                _ _ _ _ _ _ _ _ _ _ k
                _ _,
    .state _ _ _ _ _ _ _ _ _ _ l _ => k ≤ l
  | .transition _ _ _ _ _ _ _ _ _ _ _
                _ _ _ _ _ _ _ _ _ _ k
                _ _,
    .transition _ _ _ _ _ _ _ _ _ _ _
                _ _ _ _ _ _ _ _ _ _ l
                _ _ => k ≤ l
end Automaton

instance : LE Automaton where
  le := Automaton.le


structure MappingProcess
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (Input: Type 1)
    (StateChange: Type 1 → Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ s ψ x f m l a Input transport_carrier]
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
  accumulation: Tape
  input: Type Input
  computation: Type 1 → Type 1

  mapped? : Prop := observation.truth
  map: Type 1 → Type 1 := computation

class DISTINCT
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (Input: Type 1)
    (StateChange: Type 1 → Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ s ψ x f m l a Input transport_carrier]
  where
  mapping_process: MappingProcess Output Symbol η ζ φ s ψ x f m l a Input StateChange transport_carrier
  admissible? : Type 1 → Type 1 → Prop := fun c1 c2 => mapping_process.map c1 = c2 ∧ c1 = c2  -- We have managed to store a bit in the compiler again!  This is the residue of the mapping process, the part that is unchanged by the mapping.
  distinct? : Prop := ∃ c1 c2, mapping_process.map c1 = c2 ∧ c1 ≠ c2  -- We have managed to store a bit in the compiler again!  This is the distinctness condition, the part that is changed by the mapping.
  different? : Type 1 → Prop := fun c1 => ∃ c2, mapping_process.map c1 = c2 ∧ c1 ≠ c2  -- We have managed to store a bit in the compiler again!  This is the distinctness condition, the part that is changed by the mapping.
  dec_different: DecidablePred different?

inductive FiniteEncodingProcess
  where
  |finite: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → Tape →
           Fact → FiniteEncodingProcess
  |encoding: Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → Tape →
           Fact → Number → Natural → Rational → Sequence → Limit → Invariant → Computation → State → Ledger → Tape →
           Fact → FiniteEncodingProcess → FiniteEncodingProcess

structure LinearBoundedAutomata
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (encoding: FiniteEncodingProcess)
    (Input: Type 1)
    (StateChange: Type 1 → Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ s ψ x f m l a Input transport_carrier]
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
  accumulation: Tape
  input: Type Input
  computation: Type 1 → Type 1

  encoded? : Prop := observation.truth
  encode: Type 1 → Type 1 := computation
  admissible? : Type 1 → Prop := fun c1 =>
    match c1 with
    | _ => ∃ c2, encode c1 = c2  -- We have managed to store a bit in the compiler again!  This is the admissibility condition, the part that is unchanged by the encoding.


-- now, this is just the encoding of a computation.  we still have no way to describe
-- a computation.  Well, we do, but do you really believe my names yet?  Probably not.
-- I will now _convince_ you with inductive arguments that lean agrees with the names.

-- we now construct the causal universe tensor, a mapping between Fact, Number, and
-- universe number.  We gotsa have a representation of the naturals somehow, why not
-- the universe number?

class DECOMPOSABLE
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (encoding: FiniteEncodingProcess)
    (Input: Type 1)
    (StateChange: Type 1 → Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ s ψ x f m l a Input transport_carrier]
  where
  linear_bounded_automata: LinearBoundedAutomata Output Symbol η ζ φ s ψ x f m l a encoding Input StateChange transport_carrier
  admissible? : FiniteEncodingProcess → FiniteEncodingProcess → Prop := fun e1 e2 =>
     match e1, e2 with
     |
        .finite _ _ _ _ _ _ _ _ _ _ t1 _,
        .finite _ _ _ _ _ _ _ _ _ _ t2 _=> t1 ≤ t2
     |
        .finite   _ _ _ _ _ _ _ _ _ _ t1 _,
        .encoding _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _ _ _ t2
                  _ _ => t1 ≤ t2
     |
        .encoding _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _ _ _ t1
                  _ _,
        .finite _ _ _ _ _ _ _ _ _ _ t2 _=> t1 ≤ t2
     |
        .encoding _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _ _ _ t1
                  _ _,
        .encoding _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _ _ _ t2
                  _ _ => t1 ≤ t2

-- Big Endian Binary number with LE ordering.
inductive Decomposition where
  | zero : Decomposition
  | succ : Number → Decomposition → Decomposition

structure BisectionProcess
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (encoding: FiniteEncodingProcess)
    (Input: Type 1)
    (StateChange: Type 1 → Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ s ψ x f m l a Input transport_carrier]
    [DECOMPOSABLE Output Symbol η ζ φ s ψ x f m l a encoding Input StateChange transport_carrier]
    (d: Decomposition)
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
  accumulation: Tape
  input: Type Input
  computation: Type 1 → Type 1
  decomposition: Number × Symbol

  decompose? : Number → Symbol → Prop := fun n s =>
    match d with
    | .zero => n = Number.zero ∧ s = decomposition.2
    | .succ m d' => m ≠ n ∧ n ≤ m ∧ decomposition.1 ≤ m ∧ s = decomposition.2 ∧
                match d' with
                | .zero => m = Number.zero
                | .succ k _ => k ≤ m   -- lol, i bet you want this to be k = m+1, but it isn't,
                                       -- it is k = m + stress * stride + strain.  you will see

class RECURSIVE
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (encoding: FiniteEncodingProcess)
    (Input: Type 1)
    (StateChange: Type 1 → Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ s ψ x f m l a Input transport_carrier]
    [DECOMPOSABLE Output Symbol η ζ φ s ψ x f m l a encoding Input StateChange transport_carrier]
    (d: Decomposition)
  where
  bisection_process : BisectionProcess Output Symbol η ζ φ s ψ x f m l a encoding Input StateChange transport_carrier d
  admissible? : Prop := bisection_process.decompose? bisection_process.decomposition.1 bisection_process.decomposition.2


inductive Bisection where
  | zero : Rational → Number → Decomposition → Bisection
  | succ : Rational → Number → Decomposition → Bisection → Bisection

structure InverseProcess
    (Output: Fact)
    (Symbol: Type 1)
    (η: Natural)
    (ζ: Number)
    (φ: Rational)
    (s: Sequence)
    (ψ: Limit)
    (x: Invariant)
    (f: Computation)
    (m: State)
    (l: Ledger)
    (a: Tape)
    (encoding: FiniteEncodingProcess)
    (Input: Type 1)
    (StateChange: Type 1 → Type 1)
    [DecidableEq Symbol]
    (transport_carrier: Carrier Output)
    [DISTINGUISHABLE Output Symbol]
    [ADMISSIBLE Output Symbol η transport_carrier]
    [COUNTABLE Output Symbol η ζ φ transport_carrier]
    [CORRELANT Output Symbol η ζ φ s transport_carrier]
    [REAL Output Symbol η ζ φ s ψ transport_carrier]
    [RELATABLE Output Symbol η ζ φ s ψ x transport_carrier]
    [NOISY Output Symbol η ζ φ s ψ x f transport_carrier]
    [LAWFUL Output Symbol η ζ φ s ψ x f m transport_carrier]
    [ITERABLE Output Symbol η ζ φ s ψ x f m l transport_carrier]
    [COMPUTABLE Output Symbol η ζ φ s ψ x f m l a Input transport_carrier]
    [DECOMPOSABLE Output Symbol η ζ φ s ψ x f m l a encoding Input StateChange transport_carrier]
    (d: Decomposition)
    (b: Bisection)
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
  accumulation: Tape
  input: Type Input
  computation: Type 1 → Type 1
  decomposition: Number × Symbol
  projection: (symbol → Number × Symbol) -- I'm a sneaky s.o.b.  This maps the
                                         -- univsere id to a number and symbol decomposition.
                                         -- Nat is for suckers!


end Measurement
