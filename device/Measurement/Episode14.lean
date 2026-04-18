import Measurement.Episode13


namespace Measurement
class TRUE
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
    [compiled: COMPILED Value Carrier]
  where
  compiler_output: CompilerOutput Value Carrier

  is_it_true? : Prop :=
    measured.bullshit < compiled.compiler_output.satire.length ∧
    compiled.compiler_output.satire.length ≤ measured.volume

end Measurement
