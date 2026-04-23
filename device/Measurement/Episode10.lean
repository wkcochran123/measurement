
import Measurement.Episode9
set_option allowUnsafeReducibility true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100

-- Homework:
namespace Measurement

inductive SpaceTimePath
  | einstein: Fact → SpaceTimePath
  | white_hole: Fact → Type → SpaceTimePath → SpaceTimePath
  | blackhole: Prop → Type 1 → SpaceTimePath → SpaceTimePath
  | geodesic: Fact → Type i → Prop → Type (i+1) → SpaceTimePath → SpaceTimePath → SpaceTimePath

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
  converged: Fact
  sink: Type 1

  photon_torpedo: SpaceTimePath → SpaceTimePath := fun path =>
    match path with
    | .einstein fact =>
                .white_hole converged Value (.einstein fact)
    | .white_hole fact val path =>
              match fact.decTruth with
              | isTrue _ =>
                    .geodesic d.fact val d.fact.truth (ULift val) path function
              | isFalse _ =>
                    .blackhole fact.truth (ULift val) function
    | .geodesic fact val1 prop val2 _ _ =>
              match fact.decTruth with
              | isTrue _ =>
                    .geodesic d.fact
                              val1
                              prop
                              val2
                              (.white_hole converged (ULift Value) (.einstein fact))
                              (.einstein fact)
              | isFalse _ =>
                    .blackhole fact.truth sink function
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

  -- let's ask the compiler to hold the quarter we glued to the table.
  lake_build: SpaceTimePath → SpaceTimePath → Prop := fun _ _ => the_compiler.converged = d.fact


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
    function := .einstein d.fact
    converged := d.fact
  }
  source_program   := .white_hole d.fact Value (.einstein d.fact)
  compiled_program := .black_hole d.fact.truth (ULift Value) (.einstein d.fact)

inductive YarnTheory
|stokes: SpaceTimePath → Prop → YarnTheory
|fibers: SpaceTimePath → SpaceTimePath → Prop → Prop → YarnTheory → YarnTheory
|fabric: SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop → Prop → Prop → YarnTheory → YarnTheory → YarnTheory

@[reducible]
structure HeartbeatProcess
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
    [computer_science: UNIVERSAL Value Carrier]
  where
  bullshit_meter: CalculusProcess Value Carrier  -- Praise be to the heart.
  current_reading: SpaceTimePath
  accumulated_bullshit: YarnTheory

  weave? : YarnTheory → YarnTheory := fun yarn =>
     match yarn with
     |.stokes stp prop =>
              .fibers stp current_reading (prop=d.fact.truth) accumulated_bullshit
     |.fibers before after prop_before prop_after yt =>
              match (prop_before ∧ d.fact.truth) ∧ (¬ prop_after ∧  d.fact.truth) with
              | true  => .fibers after current_reading d.fact.truth prop_after yt accumulated_bullshit
              | false => .fabric before after current_reading d.fact.truth prop_after prop_before yt accumulated_bullshit accumulated_bullshit
     |.fabric _ x1 x2 p2 p1 _ _ yt =>
              .fabric x1 x2 current_reading d.fact.truth p2 p1 yt accumulated_bullshit



end Measurement
