
import Measurement.Episode10
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
    converged := Fact.Truth
    sink := Type
  }
  source_program   := .white_hole d.fact Value (.einstein d.fact)
  compiled_program := .blackhole d.fact.truth (ULift Value) (.einstein d.fact)

inductive YarnTheory
|stokes: Fact → SpaceTimePath → Prop → YarnTheory
|fibers: Fact → SpaceTimePath → SpaceTimePath → Prop → Prop → YarnTheory → YarnTheory
|fabric: Fact → Fact → SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop → Prop → Prop → YarnTheory → YarnTheory → YarnTheory

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
     |.stokes fact stp prop =>
              .fibers fact stp current_reading prop computer_science.the_compiler.converged.truth accumulated_bullshit
     |.fibers fact before after prop_before prop_after yt =>
              match fact.decTruth with
              | isTrue _ =>
                .fibers fact after current_reading prop_after fact.truth accumulated_bullshit
              | isFalse _ =>
                .fabric fact d.fact before after current_reading prop_before prop_after ¬fact.truth yt accumulated_bullshit
     |.fabric f1 f2 x1 x2 x3 p1 p2 p3 yt1 yt2 =>
              match f1.decTruth, f2.decTruth with
              | isTrue _   , isTrue _    =>
                          .fabric f1 f2 x1 x2 x3 p1 p2 p3 yt1 yt2
              | isTrue _   , isFalse _   =>
                          .fabric d.fact f2 current_reading x2 x3 computer_science.the_compiler.converged.truth p2 ¬p3 accumulated_bullshit yt2
              | isFalse _, isTrue _  =>
                          .fibers f2 x3 current_reading p3 f2.truth accumulated_bullshit
              | isFalse _, isFalse _ =>
                          .fabric f1 f2 x2 x3 current_reading ¬p2 ¬p3 f2.truth yt2 accumulated_bullshit



end Measurement
