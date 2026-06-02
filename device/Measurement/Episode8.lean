import Measurement.Episode7
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000000
set_option allowUnsafeReducibility true

namespace Measurement

universe i

instance STEP_1
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] : ADMISSIBLE Value Carrier where
  counting_process :=
    { carrier := Carrier
      count   := .zero d.fact
      iterate := fun n => match n with
        | .zero _     => .zero d.fact
        | .number _ _ _ => .number d.fact Carrier.value (.zero d.fact) }

instance COUNTABLE_ADMISSIBLE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    : COUNTABLE Value Carrier where
  index :=
    { count  := a.counting_process
      origin := .zero d.fact }

instance ENCODED_COUNTABLE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier] : ENCODED Value Carrier where
  limit_process :=
    { indexing_process := c.index
      limit            := .zero d.fact
      sequence         := .nil d.fact }

instance RESIDUE_ENCODED
    (Value: Type i)
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
    (Value: Type i)
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
    (Value: Type i)
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
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    : NUMERIC Value Carrier where
  computational_process :=
  { repeatable_process := xx.repeatable_process
    output := some (.hypothesis d.fact)
  }

instance REPRESENTABLE_NUMERIC
    (Value: Type i)
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
  { computational_process :=
      { aa.computational_process with
        closure := fun s => s }
    program := aa.computational_process.close aa.computational_process.output
    state := .program d.fact (aa.computational_process.close aa.computational_process.output)
  }
  representable? := fun _ s =>
    ⟨Computation.program d.fact s, rfl⟩

instance PHYSICAL_NUMERIC
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    : PHYSICAL Value Carrier where
  noisy_process := {
    turing_process := bb.calculation_process
    program := .halting d.fact (.program d.fact bb.calculation_process.program)
  }
  threshold := .nonhalting  d.fact
                            (.program d.fact bb.calculation_process.program)
                            (bb.calculation_process.turing_step? (.program d.fact bb.calculation_process.program))
  admissible? := fun _ _ _ => rfl    -- rofl!  This is some serious gourmet coding!
                                     -- The fact this exists as physical electrons is enough for me!




instance OBSERVED_COMPARABLE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    : OBSERVED Value Carrier where
  slip_process :=
  { physical_process := dd.physical_process
    projection       := .origin d.fact dd.physical_process.physical_process.program d.symbol
    stress           := cc.threshold
    threshold        := d.symbol
  }
  observation := ULift d.symbol

instance PRESENT_OBSERVED
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    : PRESENT Value Carrier where
  santa_claus:=
  { static_fraction := ee.slip_process
    accumulation := .t d.fact
  }
  quantum := Type i

instance MEASURABLE_PRESENT
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    : MEASURABLE Value Carrier where
  gauge_process :=
  { sensing_process := ff.santa_claus
    clock      := .field d.fact (.t d.fact)
  }

instance GUNGAN_MEASURABLE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    : GUNGAN Value Carrier where
  meesa_process :=
  { gauge_process := gg.gauge_process
    concept := .color d.fact gg.gauge_process.sensing_process.accumulation
  }

instance SOURCE_GUNGAN
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    : SOURCE Value Carrier where
  cd_process :=
  { meesa_process := hh.meesa_process
    zero := .physics d.fact hh.meesa_process.concept
  }
  one := .zero_like d.fact (.physics d.fact hh.meesa_process.concept)

instance EXECUTED_SOURCE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    : EXECUTED Value Carrier where
  compiled_process :=
  { digital_process := ii.cd_process
    source := ii
    opcode := .boot d.fact (.physics d.fact hh.meesa_process.concept)
  }

instance VALUE_EXECUTED
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    : VALUE Value Carrier where
    -- What we have here is the multiplicative identity.  from no-fucking-where
  mathematical_process := {
    compiled_process := jj.compiled_process
    mapping := fun input => match input with
      |.satire f => .satire f
      |.compile f e a => .execute f e a
      |.execute f e a => .compile f e a
  }
  monad := .satire d.fact

instance MAGNITUDE_VALUE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    : MAGNITUDE Value Carrier where
  adding_process :=
  { mathematical_process := kk.mathematical_process
    plus := kk
    sum := .zero d.fact.truth ff.santa_claus.accumulation
  }

instance SCALED_MAGNITUDE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    [ll: MAGNITUDE Value Carrier]
    : SCALED Value Carrier where
  multiplying_process :=
  { adding_process := ll.adding_process
    product := .one d.fact.truth ll.adding_process.sum
    total := .zero d.fact.truth (.t d.fact)
  }

instance LOAD_SCALED
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    [ll: MAGNITUDE Value Carrier]
    [mm: SCALED Value Carrier]
    : LOAD Value Carrier where
  basic_operation :=
  { GOSUB := mm.multiplying_process
    TEN := ff.santa_claus.accumulation
    span := .origin d.fact.truth mm.multiplying_process.product
  }

instance FINITE_ELEPHANT_LOAD
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    [ll: MAGNITUDE Value Carrier]
    [mm: SCALED Value Carrier]
    [nn: LOAD Value Carrier]
    : FINITE_ELEPHANT Value Carrier where
  galerkin_process :=
  { ANSYS_process := nn.basic_operation
    polynomial := .constant .Truth
  }

instance BULLSHIT_FINITE_ELEPHANT
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    [ll: MAGNITUDE Value Carrier]
    [mm: SCALED Value Carrier]
    [nn: LOAD Value Carrier]
    [oo: FINITE_ELEPHANT Value Carrier]
    : BULLSHIT Value Carrier where
  arm_wave_process :=
  { galerkin_process := oo.galerkin_process
    guess := .observation d.fact.truth
  }

instance PROPAGANDA_BULLSHIT
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    [ll: MAGNITUDE Value Carrier]
    [mm: SCALED Value Carrier]
    [nn: LOAD Value Carrier]
    [oo: FINITE_ELEPHANT Value Carrier]
    [pp: BULLSHIT Value Carrier]
    : PROPAGANDA Value Carrier where
  insinuation := CrusadeProcess.default Value Carrier

instance ACOLYTE_PROPAGANDA
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    [ll: MAGNITUDE Value Carrier]
    [mm: SCALED Value Carrier]
    [nn: LOAD Value Carrier]
    [oo: FINITE_ELEPHANT Value Carrier]
    [pp: BULLSHIT Value Carrier]
    [qq: PROPAGANDA Value Carrier]
    : ACOLYTE Value Carrier where
  euclid := InitiationProcess.default Value Carrier


end Measurement
