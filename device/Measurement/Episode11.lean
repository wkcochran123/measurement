
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

namespace SpaceTimePath
def le : SpaceTimePath → SpaceTimePath → Prop
  | .einstein f1, .einstein f2 =>
    f1 = f2
  | .einstein f1, .white_hole f2 _ _ =>
    f1 = f2
  | .einstein f1, .blackhole p2 _ _ =>
    f1.truth = p2
  | .einstein f1, .geodesic f2 _ p2 _ _ _ =>
    f1 = f2 ∧ f1.truth = p2
  | .white_hole f1 _ _, .einstein f2 =>
    f1 ≠ f2
  | .white_hole f1 val p1, .white_hole f2 _ p2 =>
    (f1 = f2 ∧ le p1 p2) ∨ le (.white_hole f1 val p1) p2
  | .white_hole f1 val p1, .blackhole p2 _ p3 =>
    (f1.truth = p2 ∧ le p1 p3) ∨ le (.white_hole f1 val p1) p3
  | .white_hole f1 val p1, .geodesic f2 _ p2 _ p3 p4 =>
    (f1 = f2 ∧ f1.truth = p2 ∧ (le p1 p3 ∨ le p1 p4)) ∨
      le (.white_hole f1 val p1) p3 ∨ le (.white_hole f1 val p1) p4
  | .blackhole p1 _ _, .einstein f2 =>
    p1 ≠ f2.truth
  | .blackhole p1 val p2, .white_hole f2 _ p3 =>
    (p1 ≠ f2.truth ∧ le p2 p3) ∨ le (.blackhole p1 val p2) p3
  | .blackhole p1 val p2, .blackhole p3 _ p4 =>
    (p1 = p3 ∧ le p2 p4) ∨ le (.blackhole p1 val p2) p4
  | .blackhole p1 val p2, .geodesic _ _ p3 _ p4 p5 =>
    (p1 = p3 ∧ (le p2 p4 ∨ le p2 p5)) ∨
      le (.blackhole p1 val p2) p4 ∨ le (.blackhole p1 val p2) p5
  | .geodesic f1 _ p1 _ _ _, .einstein f2 =>
    f1 ≠ f2 ∨ p1 ≠ f2.truth
  | .geodesic f1 val1 p1 val2 p2 p3, .white_hole f2 _ p4 =>
    (f1 = f2 ∧ f1.truth = p1 ∧ (le p2 p4 ∨ le p3 p4)) ∨
      le (.geodesic f1 val1 p1 val2 p2 p3) p4
  | .geodesic f1 val1 p1 val2 p2 p3, .blackhole p4 _ p5 =>
    (p1 = p4 ∧ (le p2 p5 ∨ le p3 p5)) ∨
      le (.geodesic f1 val1 p1 val2 p2 p3) p5
  | .geodesic f1 val1 p1 val2 p2 p3, .geodesic f2 _ p4 _ p5 p6 =>
    (f1 = f2 ∧ p1 = p4 ∧
      ((le p2 p5 ∧ le p3 p6) ∨ (le p2 p6 ∧ le p3 p5))) ∨
      le (.geodesic f1 val1 p1 val2 p2 p3) p5 ∨
        le (.geodesic f1 val1 p1 val2 p2 p3) p6
termination_by _ path => sizeOf path
end SpaceTimePath

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

namespace YarnTheory
def le : YarnTheory → YarnTheory → Prop
  | .stokes f1 p1 q1, .stokes f2 p2 q2 =>
    f1 = f2 ∧ SpaceTimePath.le p1 p2 ∧ q1 = q2
  | .stokes f1 p1 q1, .fibers f2 p2 p3 q2 q3 _ =>
    f1 = f2 ∧ (SpaceTimePath.le p1 p2 ∨ SpaceTimePath.le p1 p3) ∧
      (q1 = q2 ∨ q1 = q3)
  | .stokes f1 p1 q1, .fabric f2 f3 p2 p3 p4 q2 q3 q4 _ _ =>
    (f1 = f2 ∨ f1 = f3) ∧
      (SpaceTimePath.le p1 p2 ∨ SpaceTimePath.le p1 p3 ∨ SpaceTimePath.le p1 p4) ∧
        (q1 = q2 ∨ q1 = q3 ∨ q1 = q4)
  | .fibers f1 _ _ q1 q2 _, .stokes f2 _ q3 =>
    f1 ≠ f2 ∨ (q1 ≠ q3 ∧ q2 ≠ q3)
  | .fibers f1 p1 p2 q1 q2 y1, .fibers f2 p3 p4 q3 q4 y2 =>
    (f1 = f2 ∧ SpaceTimePath.le p1 p3 ∧ SpaceTimePath.le p2 p4 ∧
      q1 = q3 ∧ q2 = q4 ∧ le y1 y2) ∨
        le (.fibers f1 p1 p2 q1 q2 y1) y2
  | .fibers f1 p1 p2 q1 q2 y1, .fabric f2 f3 p3 p4 p5 q3 q4 q5 y2 y3 =>
    ((f1 = f2 ∨ f1 = f3) ∧
      (SpaceTimePath.le p1 p3 ∨ SpaceTimePath.le p1 p4) ∧
        (SpaceTimePath.le p2 p4 ∨ SpaceTimePath.le p2 p5) ∧
          (q1 = q3 ∨ q1 = q4) ∧ (q2 = q4 ∨ q2 = q5) ∧
            (le y1 y2 ∨ le y1 y3)) ∨
              le (.fibers f1 p1 p2 q1 q2 y1) y2 ∨
                le (.fibers f1 p1 p2 q1 q2 y1) y3
  | .fabric f1 f2 _ _ _ q1 q2 q3 _ _, .stokes f3 _ q4 =>
    (f1 ≠ f3 ∧ f2 ≠ f3) ∨ (q1 ≠ q4 ∧ q2 ≠ q4 ∧ q3 ≠ q4)
  | .fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2, .fibers f3 p4 p5 q4 q5 y3 =>
    ((f1 = f3 ∨ f2 = f3) ∧
      (SpaceTimePath.le p1 p4 ∨ SpaceTimePath.le p2 p4) ∧
        (SpaceTimePath.le p2 p5 ∨ SpaceTimePath.le p3 p5) ∧
          (q1 = q4 ∨ q2 = q4) ∧ (q2 = q5 ∨ q3 = q5) ∧
            (le y1 y3 ∨ le y2 y3)) ∨
              le (.fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2) y3
  | .fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2,
      .fabric f3 f4 p4 p5 p6 q4 q5 q6 y3 y4 =>
    (f1 = f3 ∧ f2 = f4 ∧
      SpaceTimePath.le p1 p4 ∧ SpaceTimePath.le p2 p5 ∧ SpaceTimePath.le p3 p6 ∧
        q1 = q4 ∧ q2 = q5 ∧ q3 = q6 ∧
          ((le y1 y3 ∧ le y2 y4) ∨ (le y1 y4 ∧ le y2 y3))) ∨
            le (.fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2) y3 ∨
              le (.fabric f1 f2 p1 p2 p3 q1 q2 q3 y1 y2) y4
termination_by _ yarn => sizeOf yarn
end YarnTheory

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
                .fabric fact d.fact before after current_reading prop_before prop_after (¬fact.truth) yt accumulated_bullshit
     |.fabric f1 f2 x1 x2 x3 p1 p2 p3 yt1 yt2 =>
              match f1.decTruth, f2.decTruth with
              | isTrue _   , isTrue _    =>
                          .fabric f1 f2 x1 x2 x3 p1 p2 p3 yt1 yt2
              | isTrue _   , isFalse _   =>
                          .fabric d.fact f2 current_reading x2 x3 computer_science.the_compiler.converged.truth p2 (¬p3) accumulated_bullshit yt2
              | isFalse _, isTrue _  =>
                          .fibers f2 x3 current_reading p3 f2.truth accumulated_bullshit
              | isFalse _, isFalse _ =>
                          .fabric f1 f2 x2 x3 current_reading (¬p2) (¬p3) f2.truth yt2 accumulated_bullshit



end Measurement
