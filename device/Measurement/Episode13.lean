import Measurement.Episode12
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

universe i

inductive Measurement
|origin: Fact → Number → Type i → Measurement
|distance: Fact → Number → Number → Type i → Type (i+1) → Measurement → Measurement
|speed: Fact → Number → Number → Number → Type i → Type (i+1) → Type i →  Measurement → Measurement → Measurement

namespace Measurement
def le : Measurement → Measurement → Prop := fun t1 t2 =>
  match t1, t2 with
  | .origin f1 num1 _, origin f2 num2 _ => (f1 = f2) ∧ num1 ≤ num2
  | .origin _ _ _ , _ => True
  | _ , .origin _ _ _ => False
  | .distance f1 _ length1 _ _ _, .distance f2 _ length2 _ _ _ => (f1 = f2) ∧ length1 ≤ length2
  | .distance _ _ _ _ _ _, _ => True
  | _, .distance _ _ _ _ _ _ => False
  | .speed f1 _ _ speed1 _ _ _ _ _ , .speed f2 _ _ speed2 _ _ _ _ _ => (f1 = f2) ∧ speed1 ≤ speed2
end Measurement

instance : LE Measurement where
  le := Measurement.le

@[reducible]
structure LeanProcess
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    [executable: HALTED Value Carrier]
  where
  description: ElaborationProcess Value Carrier
  length: Number
  velocity: Measurement
  projection: Type i


  evolve? : Measurement → Measurement := fun x =>
    match x with
    | .origin fact number _ => .distance fact number length Value (ULift.{i+1} Value) velocity
    | .distance fact x1 x2 _ _ v =>
                                .speed fact x1 x2 length Value (ULift.{i+1} Value) projection v velocity
    | .speed fact _ x2 x3 _ _ _ _ v =>
                                .speed fact x2 x3 length Value (ULift.{i+1} Value) projection v velocity


@[reducible]
class MEASURED
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    [executable: HALTED Value Carrier]
  where
  satire: LeanProcess Value Carrier

  bounded? : Measurement → Measurement → Prop := fun a b =>
    Measurement.le a b


instance MEASURED_HALTED
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    [executable: HALTED Value Carrier]
    : MEASURED Value Carrier where
  satire :=
  { description := executable.scientific_paper
    length := Carrier.value
    velocity := .origin d.fact Carrier.value Value
    projection := ULift.{i} (ULift.{i} (ULift.{i} Value))  -- Hmm... wonder what this could mean?
  }


end Measurement
