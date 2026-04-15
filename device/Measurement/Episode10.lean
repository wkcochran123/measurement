
import Measurement.Episode9

-- Homework:
namespace Measurement

structure CalculusProcess
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
  where
  reading: BigRedDogProcess Value Carrier  -- Parents, read to your kids.  They are the future.
  invariant_description: SpaceTimePath

  ouija_board: SpaceTimePath → SpaceTimePath := fun path =>
    match path with
    | .white_hole fact representation => .white_hole fact representation invariant_description
    | .black_hole f1 _ f2 horizon path' => .black_hole f1 horizon f2 ULift(horizon) invariant_description
    | .geodesic f1 path1 f2 path2 send receive => .geodesic ¬f1 path2 ¬f1 path1 receive send invariant_description


class UNIVERSAL
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
  where
  the_compiler: CalculusProcess Value Carrier  -- Praise be to the universal compiler.
  compiler_theory: SpaceTimePath → SpaceTimePath

  -- Riding the train into the city sux ass, but at least you can write stupid Lean while you do it.
  lake_build: SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop := fun path1 path2 path3 =>
  compiler_theory path1 = path2 ∧ compiler_theory path2 = path3


inductive YarnTheory
|bulk: SpaceTimePath → SpaceTimePath → Prop → Integral
|boundary: SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop → Prop → Integral → Integral

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
    [delta: UNIVERSAL Value Carrier]
  where
  bullshit_meter: CalculusProcess Value Carrier  -- Praise be to the heart.
  bullshit_theory: SpaceTimePath → SpaceTimePath → SpaceTimePath → Prop → Prop
  accumulated_bullshit: YarnTheory

  differentiate: Prop → Prop → YarnTheory := fun f1 f2 =>
    match d.dec_distinct f1, d.dec_distinct f2 with
    | isTrue _,  isTrue _  => .fibers epsilon.invariant_description epsilon.invariant_description True
    | isFalse _, isFalse _ => .fibers epsilon.invariant_description epsilon.invariant_description True
    | _, _                 => .bulk epsilon.invariant_description
                                    epsilon.invariant_description
                                    epsilon.invariant_description
                                    (f1 ∧ ¬f2)
                                    (¬f1 ∧ f2)
                                    accumulated_bullshit


/-

def program : CarrierProcess FiniteGaugeTheoryOfMeasurement := sorry

-- Problem 1: Implement de Morgan's law of the excluded middle.
instance : DISTINGUISHABLE FiniteGaugeTheoryOfMeasurement program := sorry

-- My answer:
def program : CarrierProcess FiniteGaugeTheoryOfMeasurement where
--                  +---------------------------    Weierstrauss Approximation Theorem  cuz Fuck the Continuum Hypothesis
--                  |                               I can make that three pointer all day long.  Swish.
--                  V
  symbol := { truth := False, decTruth := Decidable.isFalse (fun h => h) }
  value  := .one Fact.Truth (.zero Fact.Truth)


-- I believe this demonstrates Euler-Lagrange.  I mean, it had to demonstrate
-- a solution to Euler-Lagrange to compile.
-/


end Measurement
