
import Measurement.Episode9
set_option allowUnsafeReducibility true
set_option maxHeartbeats 4000000

-- Homework:
namespace Measurement

inductive SpaceTimePath
  | einstein: Prop → SpaceTimePath
  | white_hole: Prop → Type → SpaceTimePath → SpaceTimePath
  | black_hole: Prop → Type 1 → SpaceTimePath → SpaceTimePath
  | geodesic: Prop → Type i → Prop → Type (i+1) → SpaceTimePath → SpaceTimePath → SpaceTimePath

@[reducible]
structure CalculusProcess
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
    [account: WITNESSED Value Carrier]
    [epsilon: LOCAL Value Carrier]
  where
  derivative: BigRedDogProcess Value Carrier  -- Parents, read to your kids.  They are the future.
  function: SpaceTimePath
  converged: Prop

  photon_torpedo: SpaceTimePath → SpaceTimePath := fun path =>
    match path with
    | .einstein prop                            => .white_hole d.fact.truth Value (.einstein prop)
    | .white_hole prop val path                 => .geodesic d.fact.truth val prop (ULift val) path function
    | .geodesic prop1 val1 prop2 val2 before after =>
                                          match (prop1 = prop2) with  -- variance check
                                          | true  => .geodesic prop1 val1 prop2 val2 after function  -- covariant: keep threading
                                          | false => .black_hole prop1 val2 after                    -- contravariant: collapse
    | .blackhole prop val after => .blackhole prop val after


@[reducible]
class UNIVERSAL
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
    [account: WITNESSED Value Carrier]
    [epsilon: LOCAL Value Carrier]
  where
  the_compiler: CalculusProcess Value Carrier  -- Praise be to the universal compiler.
  source_program: SpaceTimePath
  compiled_program: SpaceTimePath

  -- Riding the train into the city sux ass, but at least you can write stupid Lean while you do it.
  lake_build: SpaceTimePath → SpaceTimePath → Prop := fun _ _ => the_compiler.converged = d.fact.truth


instance UNIVERSAL_LOCAL
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
    [account: WITNESSED Value Carrier]
    [epsilon: LOCAL Value Carrier]
    : UNIVERSAL Value Carrier where
  the_compiler :=
  { derivative := epsilon.theory
    function := .einstein d.fact.truth
    converged := d.fact.truth
  }
  source_program   := .white_hole d.fact.truth Value (.einstein d.fact.truth)
  compiled_program := .black_hole d.fact.truth (ULift Value) (.einstein d.fact.truth)

inductive YarnTheory
|fibers: SpaceTimePath → SpaceTimePath → Prop → YarnTheory → YarnTheory
|fabric: SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop → Prop → YarnTheory → YarnTheory → YarnTheory

@[reducible]
structure HeartbeatProcess
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
    [computer_science: UNIVERSAL Value Carrier]
  where
  bullshit_meter: CalculusProcess Value Carrier  -- Praise be to the heart.
  last_reading: SpaceTimePath
  current_reading: SpaceTimePath
  next_reading: SpaceTimePath
  accumulated_bullshit: YarnTheory

  differential: Fact → Fact → YarnTheory := fun f1 f2 =>
    match f1.decTruth, f2.decTruth with
    | isTrue _,  isTrue _  => .fibers computer_science.source_program computer_science.compiled_program d.fact.truth accumulated_bullshit
    | isFalse _, isFalse _ => .fibers computer_science.source_program computer_science.source_program (¬d.fact.truth) accumulated_bullshit
    | _, _ => .fabric last_reading current_reading next_reading (f1.truth = ¬f2.truth) (¬f1.truth = f2.truth) accumulated_bullshit accumulated_bullshit


end Measurement
