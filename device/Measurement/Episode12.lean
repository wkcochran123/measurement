
import Measurement.ComputerProgram
import Measurement.Calibration.LeanCalibration
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

universe i

@[reducible]
class LOGICAL
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [imaginary: REAL Value Carrier]
    [delta: UNIVERSAL Value Carrier]
  where
  feelings: HeartbeatProcess Value Carrier imaginary delta
  ekg: Calibration.EKG

  logical? : YarnTheory → YarnTheory → Prop := fun a b =>
    YarnTheory.le a b

instance LOGICAL_UNIVERSAL
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    : LOGICAL Value Carrier where
  feelings :=
  { bullshit_meter := delta.the_compiler
    current_reading := .white_hole d.fact Value (.einstein d.fact)
    accumulated_bullshit := .stokes d.fact (.einstein d.fact) d.fact.truth
  }
  ekg := Calibration.EKG.executed

namespace ComputerProgram
def le
    (Value : Type i)
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
    [account: WITNESSED Value Carrier] [REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    : ComputerProgram → ComputerProgram → Prop
  | .boolean p1 p2 p3 t1 t2 t3 program1,
      .boolean p4 p5 p6 t4 t5 t6 program2 =>
    let before := ComputerProgram.boolean p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.boolean p4 p5 p6 t4 t5 t6 program2
    prop.ekg.booleanProgram? before after
  | .transform p1 p2 t1 t2 program1,
      .boolean p3 p4 p5 t3 t4 t5 program2 =>
    let before := ComputerProgram.transform p1 p2 t1 t2 program1
    let after := ComputerProgram.boolean p3 p4 p5 t3 t4 t5 program2
    prop.ekg.transformBoolean? before after
  | .boolean p1 p2 p3 t1 t2 t3 program1,
      .transform p4 p5 t4 t5 program2 =>
    let before := ComputerProgram.boolean p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.transform p4 p5 t4 t5 program2
    prop.ekg.booleanTransform? before after
  | _, _ => False
end ComputerProgram

@[reducible]
structure ElaborationProcess
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [LOCAL Value Carrier real] (imaginary: REAL Value Carrier)
    [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
  where
  stamina: HeartbeatProcess Value Carrier imaginary delta
  calibration: Calibration.EKG
  computer_state:  ComputerProgram

  execute: ComputerProgram → ComputerProgram := fun op_code =>
      match op_code with
      | .load load_prop load_type =>
                  .transform load_prop (¬load_prop) load_type (ULift.{i+1} Value)
                    (.load load_prop load_type)
      | .transform p1 p2 t t1 program =>
                  .boolean p1 p2 d.fact.truth t t1 (ULift.{i+1} t1) program

      | .boolean outer_p1 outer_p2 outer_p3 outer_t _ outer_ti outer_program =>
                    if calibration.outgrown? op_code then
                      .load (¬outer_p1 ∧ ¬outer_p2 ∧ outer_p3) outer_t
                    else
                      match d.fact.decTruth with
                        | isTrue _  => .boolean outer_p2 outer_p3 d.fact.truth
                                          outer_t (ULift.{i+1} outer_t) outer_ti outer_program
                        | isFalse _ => .load (¬outer_p1 ∧ ¬outer_p2 ∧ outer_p3) outer_t




@[reducible]
class HALTED
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
  where
  scientific_paper: ElaborationProcess Value Carrier real

  halted? : ComputerProgram → ComputerProgram → Prop := fun _ program =>
    match program with
    | .load p _ => p
    | .transform p _ _ _ _ => p
    | .boolean p _ _ _ _ _ _ => p


instance HALTED_LOGICAL
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    : HALTED Value Carrier where
  scientific_paper :=
    let feelings : HeartbeatProcess Value Carrier imaginary delta := prop.feelings
    let ekg : Calibration.EKG := prop.ekg
    { stamina := feelings
      calibration := ekg
      computer_state := (.load Fact.Truth.truth Value)
    }

end Measurement
