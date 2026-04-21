import Measurement.Episode6

namespace Measurement

instance STEP_1
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] : ADMISSIBLE Value Carrier where
  counting_process :=
    { carrier := Carrier
      count   := .zero d.fact
      iterate := fun n => match n with
        | .zero _     => .zero d.fact
        | .number _ _ _ => .number d.fact Carrier.value (.zero d.fact) }

instance COUNTABLE_ADMISSIBLE
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    : COUNTABLE Value Carrier where
  index :=
    { count  := a.counting_process
      origin := .zero d.fact }

instance ENCODED_COUNTABLE
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier] : ENCODED Value Carrier where
  limit_process :=
    { indexing_process := c.index
      limit            := .zero d.fact
      sequence         := .nil d.fact }

instance RESIDUE_ENCODED
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] : RESIDUE Value Carrier where
  cauchy_process :=
    { limit_process  := e.limit_process
      value          := .zero d.fact
      accumulation   := .nil d.fact }

instance BINARY_RESIDUE
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier] : BINARY Value Carrier where
  observation_process :=
    { cauchy_process := r.cauchy_process
      before         := .nil d.fact
      after          := .nil d.fact }
  bit := .initial_condition d.fact r.cauchy_process.accumulation
  zero := .nil d.fact
  one  := .nil d.fact

instance REPEATABLE_BINARY
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    : REPEATABLE Value Carrier where
  repeatable_process :=
  {
    observation_process := b.observation_process
    stimulus := .initial_condition d.fact b.zero
    expectation := .hypothesis d.fact b.bit
  }

instance NUMERIC_REPEATABLE
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    : REPRESENTABLE Value Carrier where
  calculation_process :=
  { computational_process := aa.computational_process
    program := match aa.computational_process.output with
    |some x => x
    |none => .hypothesis d.fact xx.repeatable_process.expectation
    state := .program d.fact (match aa.computational_process.output with
      |some x => x
      |none => .hypothesis d.fact xx.repeatable_process.expectation)
  }
  representable? := fun _ s =>
    ⟨Computation.program d.fact s,
      match aa.computational_process.output with
      | none   => rfl
      | some _ => rfl⟩

end Measurement
