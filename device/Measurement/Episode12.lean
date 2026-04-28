
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

  logical? : YarnTheory → YarnTheory → Prop := fun a b =>
    YarnTheory.le a b

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

namespace ComputerProgram
def le : ComputerProgram → ComputerProgram → Prop
  | .load f1 p1 _, .load f2 p2 _ =>
    f1 = f2 ∧ p1 = p2
  | .load f1 p1 _, .transform f2 _ p2 _ _ _ _ =>
    f1 = f2 ∧ p1 = p2
  | .load f1 p1 _, .boolean f2 _ _ p2 _ _ _ _ _ _ =>
    f1 = f2 ∧ p1 = p2
  | .transform f1 f2 p1 p2 _ _ _, .load f3 p3 _ =>
    (f1 ≠ f3 ∧ f2 ≠ f3) ∨ (p1 ≠ p3 ∧ p2 ≠ p3)
  | .transform f1 f2 p1 p2 t1 t2 c1, .transform f3 f4 p3 p4 _ _ c2 =>
    (f1 = f3 ∧ f2 = f4 ∧ p1 = p3 ∧ p2 = p4 ∧ le c1 c2) ∨
      le (.transform f1 f2 p1 p2 t1 t2 c1) c2
  | .transform f1 f2 p1 p2 t1 t2 c1, .boolean f3 f4 _ p3 p4 _ _ _ _ c2 =>
    (f1 = f3 ∧ f2 = f4 ∧ p1 = p3 ∧ p2 = p4 ∧ le c1 c2) ∨
      le (.transform f1 f2 p1 p2 t1 t2 c1) c2
  | .boolean f1 f2 f3 p1 p2 p3 _ _ _ _, .load f4 p4 _ =>
    (f1 ≠ f4 ∧ f2 ≠ f4 ∧ f3 ≠ f4) ∨ (p1 ≠ p4 ∧ p2 ≠ p4 ∧ p3 ≠ p4)
  | .boolean f1 f2 _ p1 p2 _ t1 t2 t3 c1, .transform f4 f5 p4 p5 _ _ c2 =>
    (f1 = f4 ∧ f2 = f5 ∧ p1 = p4 ∧ p2 = p5 ∧ le c1 c2) ∨
      le (.boolean f1 f2 f1 p1 p2 p1 t1 t2 t3 c1) c2
  | .boolean f1 f2 f3 p1 p2 p3 t1 t2 t3 c1, .boolean f4 f5 f6 p4 p5 p6 _ _ _ c2 =>
    (f1 = f4 ∧ f2 = f5 ∧ f3 = f6 ∧
      p1 = p4 ∧ p2 = p5 ∧ p3 = p6 ∧ le c1 c2) ∨
        le (.boolean f1 f2 f3 p1 p2 p3 t1 t2 t3 c1) c2
termination_by _ program => sizeOf program
end ComputerProgram

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
      | .load load_fact load_prop load_type =>
                  .transform d.fact Fact.Truth load_prop (¬load_prop) load_type (ULift Value)
                    (.load load_fact load_prop load_type)
      | .transform f1 f2 p1 p2 t t1 program =>
                  .boolean f1 f2 d.fact p1 p2 d.fact.truth t t1 (ULift t1) program

      | .boolean _ outer_f2 outer_f3 outer_p1 outer_p2 outer_p3 outer_t _ outer_ti outer_program =>
                    match d.fact.decTruth with
                        | isTrue _  => .boolean outer_f2 outer_f3 d.fact outer_p2 outer_p3 d.fact.truth
                                          outer_t (ULift outer_t) outer_ti outer_program
                        | isFalse _ => .load d.fact (¬outer_p1 ∧ ¬outer_p2 ∧ outer_p3) outer_t




@[reducible]
class HALTED
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
  scientific_paper: ElaborationProcess Value Carrier

  halted? : ComputerProgram → ComputerProgram → Prop := fun _ program =>
    match program with
    | .load _ _ _ => False
    | .transform _ _ _ _ _ _ _ => False
    | .boolean _ _ _ _ _ _ _ _ _ _ => True


instance HALTED_LOGICAL
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
    : HALTED Value Carrier where
  scientific_paper :=
  { stamina := prop.feelings
    computer_state := (.load Fact.Truth Fact.Truth.truth Value)
  }

end Measurement
