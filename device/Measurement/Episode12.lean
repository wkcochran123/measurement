
import Measurement.Episode11
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000000
set_option allowUnsafeReducibility true

namespace Measurement

@[reducible]
class LOGICAL
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
  where
  feelings: HeartbeatProcess Value Carrier

instance LOGICAL_UNIVERSAL
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    : LOGICAL Value Carrier where
  feelings :=
  { bullshit_meter := delta.the_compiler
    current_reading := .white_hole d.fact Value (.einstein d.fact)
    accumulated_bullshit := .stokes d.fact (.einstein d.fact) d.fact.truth
  }

inductive ComputerProgram
| load: Fact → Prop → Type → ComputerProgram
| transform:   Fact → Fact → Prop → Prop → Type → Type 1 → ComputerProgram → ComputerProgram
| boolean:   Fact → Fact → Fact → Prop → Prop → Prop → Type → Type 1 → Type i → ComputerProgram → ComputerProgram

@[reducible]
structure ElaborationProcess
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
  where
  stamina: HeartbeatProcess Value Carrier
  computer_state:  ComputerProgram

  execute: ComputerProgram → ComputerProgram := fun op_code =>
      match op_code with
      |.load fact prop type =>
                    .transform d.fact Fact.Truth prop ¬prop type Type (.load fact prop type)
      |.transform f1 f2 p1 p2 t t1 program =>
                    match program with
    match program with
    | .load fact prop type =>
        match f1.decTruth, f2.decTruth with
        | isTrue _,  isTrue _  =>
            .transform f1 f2 p1 p2 t t1 program                         -- T=T: fixed point
        | isTrue _,  isFalse _ =>
            .transform d.fact f2 p1 ¬p2 t Type (.load fact prop type)   -- T=F: shock, negate p2
        | isFalse _, isTrue _  =>
            .transform f2 d.fact p2 p1 t Type (.load fact prop type)    -- F=T: recovery, swap facts
        | isFalse _, isFalse _ =>
            .transform f1 f2 p1 p2 t t1 program                         -- F=F: Jupyter halt, identity
    | .transform f1' f2' p1' p2' t' t1' _ =>
        -- two transforms deep: three levels of history → eligible for boolean
        match f1.decTruth, f2.decTruth with
        | isTrue _, isTrue _  =>
            .boolean f1 f2 f1' p1 p2 p1' t t1 t' program               -- T=T: promote, CMB threshold
        | isTrue _, isFalse _ =>
            .boolean d.fact f2 f1' p1 ¬p2 p1' t Type t' program        -- T=F: promote under shock
        | isFalse _, isTrue _  =>
            .transform f2 d.fact p2 p1 t t1 program                     -- F=T: stay, not ready yet
        | isFalse _, isFalse _ =>
            .transform f1 f2 p1 p2 t t1 program                         -- F=F: halt
    | .boolean f1' f2' f3' p1' p2' p3' t' t1' t    |.boolean f1 f2 f3 p1 p2 p3 t t1 ti program =>
        match d.fact.decTruth with
            | isTrue _  => .boolean f2 f3 f1 p2 p3 p1 t t t program
            | isFalse _ => .load d.fact (p1 ∧ p2 ∧ p3) t




@[reducible]
class HALTED
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier]
    [scaled: SCALED Value Carrier]
    [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier]
    [model: BULLSHIT Value Carrier]
    [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
    [epsilon: LOCAL Value Carrier]
    [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
  where
  scientific_paper: ElaborationProcess Value Carrier
  hypothesis: Fact   -- So, how true is true = true?
  result: Prop       -- Guess we will find out.

  believe? : Prop → Fact := fun guess =>
    { truth := guess ≠ hypothesis.truth,   -- Our expectation is that one CANNOT compute halting.
      decTruth := Classical.propDecidable (guess ≠ hypothesis.truth) }


end Measurement
