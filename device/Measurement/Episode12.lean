import Measurement.Episode11
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000000

namespace Measurement
inductive Measurement
|distance: Number → Measurement → Measurement
|speed: Number → Number → Measurement → Measurement → Measurement

namespace Measurement
def le : Measurement → Measurement → Prop := fun t1 t2 =>
  match t1, t2 with
  | .distance a _ , .distance b _ => a ≤ b
  | .distance a _, .speed _ b _ _ => a ≤ b
  | .speed _ b _ _, .distance a _ => a ≤ b
  | .speed _ a _ _, .speed _ b _ _ => a ≤ b
end Measurement

instance : LE Measurement where
  le := Measurement.le

structure LeanProcess
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
    [executable: HALTED Value Carrier]
  where
  description: ElaborationProcess Value Carrier
  length: Number
  velocity: Measurement

  evolve? : Measurement → Measurement := fun x =>
    match x with
    | .distance _ _ => .distance length velocity
    | .speed _ pos2 _ current_speed => .speed pos2 length current_speed velocity


class MEASURED
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
    [executable: HALTED Value Carrier]
  where
  satire: LeanProcess Value Carrier
  bullshit: Number
  volume: Number

  piled_high_and_deep? : Measurement → Measurement → Measurement := fun x_1 x_2 =>
    match x_1 with
    | .distance _ _ => .speed bullshit volume x_2 x_2
    | .speed _ pos2 _ current_speed => .speed pos2 bullshit current_speed x_2


end Measurement
