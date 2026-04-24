import Measurement.Episode13

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

inductive CompilerTape where
  | boot    : Fact → Type → CompilerTape
  | strap   : Fact → Fact → Type → Type 1 → CompilerTape → CompilerTape
  | compute : Fact → Fact → Prop → Type → Type 1 → Type i → CompilerTape → CompilerTape

namespace CompilerTape
def le : CompilerTape → CompilerTape → Prop := fun t1 t2 =>
  match t1, t2 with
  | .boot _ _         , _                 => True
  | _                   , .boot _ _       => False
  | .strap f1 _ _ _ _   , .strap f2 _ _ _ _ => f1 = f2
  | _                   , .strap _ _ _ _ _  => False
  | .strap _ _ _ _ _    , _                 => True
  | .compute f1 f2 _ _ _ _ _ , .compute f3 f4 _ _ _ _ _ => (f1 = f3) ∧ (f2 ≠ f4)

def lt : CompilerTape → CompilerTape → Prop := fun n1 n2 => le n1 n2 ∧ ¬ le n2 n1

end CompilerTape

instance : LE CompilerTape where
  le := CompilerTape.le
instance : LT CompilerTape where
  lt := CompilerTape.lt

@[reducible]
structure CompilerOutput
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
  where
  satire: LeanProcess Value Carrier
  tape: CompilerTape

  emit?: CompilerTape → CompilerTape := fun t =>
    match t with
    | .boot a b                => .strap a d.fact b (ULift b) tape
    | .strap f1 f2 t t1 symbol => .compute f1 f2 d.fact.truth t t1 (ULift t1) symbol
    | .compute f1 f2 _ t t1 t2 remainder =>
          match f1.decTruth,f2.decTruth with
          | isTrue _     , isTrue _    =>  .boot Fact.Truth Value
          | isTrue _     , isFalse _   =>  .compute f1 d.fact d.fact.truth t t1 t2 remainder
          | isFalse _    , isTrue _    =>  .compute d.fact f2 d.fact.truth t t1 t2 remainder
          | isFalse _    , isFalse _   =>  .strap Fact.Truth Fact.Truth t t1 remainder

@[reducible]
class COMPILED
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
  where
  compiler_output: CompilerOutput Value Carrier
  object_file: CompilerTape

instance COMPILED_MEASURED
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
    : COMPILED Value Carrier where
  compiler_output :=
  { satire := measured.satire
    tape := (.boot Fact.Truth Value)
  }
  object_file := .strap Fact.Truth Fact.Truth Value (ULift Value) (.boot Fact.Truth Value)


end Measurement
