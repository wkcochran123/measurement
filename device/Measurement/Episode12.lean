
import Measurement.ComputerProgram
import Measurement.Calibration.LeanCalibration
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
  ekg: Calibration.EKG

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
  ekg := Calibration.EKG.raw

namespace ComputerProgram
def le
    (Value : Type)
    (Carrier : CarrierProcess Value)
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
    : ComputerProgram → ComputerProgram → Prop
  | .boolean f1 f2 f3 p1 p2 p3 t1 t2 t3 program1,
      .boolean f4 f5 f6 p4 p5 p6 t4 t5 t6 program2 =>
    let before := ComputerProgram.boolean f1 f2 f3 p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.boolean f4 f5 f6 p4 p5 p6 t4 t5 t6 program2
    (f1 = f4 ∧ f2 = f5 ∧ f3 = f6 ∧
      prop.ekg.booleanProgram? before after)
  | .transform f1 f2 p1 p2 t1 t2 program1,
      .boolean f3 f4 f5 p3 p4 p5 t3 t4 t5 program2 =>
    let before := ComputerProgram.transform f1 f2 p1 p2 t1 t2 program1
    let after := ComputerProgram.boolean f3 f4 f5 p3 p4 p5 t3 t4 t5 program2
    prop.ekg.transformBoolean? before after
  | .boolean f1 f2 f3 p1 p2 p3 t1 t2 t3 program1,
      .transform f4 f5 p4 p5 t4 t5 program2 =>
    let before := ComputerProgram.boolean f1 f2 f3 p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.transform f4 f5 p4 p5 t4 t5 program2
    prop.ekg.booleanTransform? before after
  | _, _ => False
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
  calibration: Calibration.EKG
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
    let feelings : HeartbeatProcess Value Carrier := prop.feelings
    let ekg : Calibration.EKG := prop.ekg
    { stamina := feelings
      calibration := ekg
      computer_state := (.load Fact.Truth Fact.Truth.truth Value)
    }

end Measurement
