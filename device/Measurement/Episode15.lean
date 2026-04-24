import Measurement.Episode14

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000000
set_option allowUnsafeReducibility true


namespace Measurement

inductive Measurement where
| zero  : Fact → CompilerTape → Measurement
| one   : Fact → Number → CompilerTape → CompilerTape → Measurement → Measurement
| rest  : Fact → Fact → Prop → Number → Number → Number → CompilerTape → CompilerTape →
                      Measurement → Measurement → Measurement

namespace Measurement
  def le : Measurement → Measurement → Prop
  | .zero f _                  , .zero g _                  => f.truth = g.truth
  | .zero _ _                  , _                          => True  -- Zero is the origin for all

  | .one _ _ _ _ _             , .zero _                    => False
  | .one p1 n1' _ _ _          , .one p2 n2' _ _ _          =>
                                                    match p1.decTruth, p2.decTruth with
                                                    | isTrue _,  isTrue _  => le n1' n2'
                                                    | isFalse _, isFalse _ => le n2' n1'
                                                    | isTrue _,  isFalse _ => False
                                                    | isFalse _, isTrue _  => True
  | .one _ _ _ _ _             , rest _ _ _ _ _ _ _ _ _ _   => True

  | .rest _ _ _ _ _ _ _ _ _ _  , .zero _ _                  => False
  | .rest _ _ _ _ _ _ _ _ _ _  , .one _ _ _ _ _             => False

  | .rest f1 g1 p1 n11 n12 n13 t11 t12 m11 m12,
  .rest f2 g2 p2 n21 n22 n23 t21 t22 m21 m22 =>
    (f1.truth = f2.truth) ∧
    (g1.truth = g2.truth) ∧
    (p1 -> p2) ∧
    (n13 ≤ n23) ∧
    le m11 m21 ∧
    le m12 m22

def lt: Measurement → Measurement → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Measurement


structure NumberOutput
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
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier] where
  compiler_output: CompilerOutput Value Carrier
  measurement: Measurement
  stress: Number
  atreyu: Number := Carrier.event Carrier.value   -- Delicious Ouroboros!!


  enumerate: Measurement → Measurement := fun measurement =>
  match measurement with
  |.zero _ object_file   =>
              .one d.fact stress object_file compiler_output.object_file measurement
  |.one fact last_stress prev_object last_object last_measurement =>
              .rest fact d.fact d.fact.truth last_stress stress strain prev_object last_object last_measurement measurement
  | .rest f1 f2 rel n1 n2 n3 prev_object last_object m1 m2 =>
    .rest f2 d.fact (((f2.truth = d.fact.truth) ∧ (n1 ≤ n2))∨((f2.truth ≠ d.fact.truth ∧ n2 ≤ n1))) n3 stress strain last_object compiler_output.object_file m2 measurement






@[reducible]
class TrueOutput
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
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
  where


instance TRUE_COMPILED
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
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
    : TRUE Value Carrier where
  compiler_output =
  { }


end Measurement
