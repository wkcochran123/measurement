import Measurement.Episode13

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000000
set_option allowUnsafeReducibility true

namespace Measurement

inductive CompilerTape where
  | boot    : Fact → Type → CompilerTape
  | strap   : Fact → Type → Type 1 → CompilerTape → CompilerTape
  | compute : Fact → Type → Type i → Prop → Type → Type (i+1) → CompilerTape → CompilerTape → CompilerTape

namespace CompilerTape
def le : CompilerTape → CompilerTape → Prop := fun t1 t2 =>
  match t1, t2 with
  | .boot _ _ _ , .boot _ _ _ => True
  | .boot _ _ _ , .strap _ _ _ _ _ => True
  | .strap _ _ _ _ _ , .boot _ _ _ => False
  | .strap _ _ _ _ a , .strap _ _ _ _ b => le a b
  termination_by _ t2 => sizeOf t2

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
    [measured: MEASURED Value Carrier]
  where
  satire: LeanProcess Value Carrier
  tape: CompilerTape
  symbol : Type Value

  emit?: CompilerTape → CompilerTape := fun t =>
    match t with
    | .boot a b _ => .boot a b tape
    | .strap a b c prior _ => .strap a b c prior tape

@[reducible]
class COMPILED
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
    [measured: MEASURED Value Carrier]
  where
  compiler_output: CompilerOutput Value Carrier
  object_file: CompilerTape

  load_opcode: Type Value → CompilerTape := fun _ => object_file

end Measurement
