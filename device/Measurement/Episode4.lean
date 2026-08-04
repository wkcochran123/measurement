/-
-/

-- Have I convinced you yet of the dangers of using other peoples imports?
import Measurement.Episode3


-- Use this at your own risk.  If you accidentally program something that requires the violation of
-- the halting problem to represent, you might find yourself waiting a few minutes for the compiler
-- as it slowly enumerates ALL of computation to find your program.

-- -O2 is for suckers, this thing enumerates computation and finds the one that we want and copies
-- the input into the output. That's how it compiles!  Kolmogorov eat your heart out, I put a ring on it!

-- Literally, algebraic ring incoming.
namespace Measurement

universe i

@[reducible]
structure ArmWaveProcess   -- 3306
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [DISTINGUISHABLE Value Carrier]
    [ADMISSIBLE Value Carrier]
    [COUNTABLE Value Carrier]
    [ENCODED Value Carrier]
    [RESIDUE Value Carrier]
    [BINARY Value Carrier]
    [REPEATABLE Value Carrier]
    [NUMERIC Value Carrier]
    [REPRESENTABLE Value Carrier]
    [PHYSICAL Value Carrier]
    [COMPARABLE Value Carrier]
    [OBSERVED Value Carrier]
    [PRESENT Value Carrier]
    [MEASURABLE Value Carrier]
    [GUNGAN Value Carrier]
    [SOURCE Value Carrier]
    [EXECUTED Value Carrier]
    [VALUE Value Carrier]
    [MAGNITUDE Value Carrier]
    [SCALED Value Carrier]
    [LOAD Value Carrier]
    [FINITE_ELEPHANT Value Carrier]
  where
  galerkin_process : GalerkinProcess Value Carrier
  guess: Spline

  reticulate?: Spline → Spline := fun input =>
    match input with
    | .observation prop => .knot prop matter.galerkin_process.polynomial (.observation prop)
    | .knot prop poly _ => .knot prop poly guess
    | .interpolant prop _ poly2 prior _ => .interpolant prop poly2 matter.galerkin_process.polynomial prior guess

class BULLSHIT  -- 2733              Bullshit is __STRICTLY__ conserved.
    (Value: Type i)
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
  where
  arm_wave_process : ArmWaveProcess Value Carrier
  interpolate? : Spline → Spline → Prop := fun a b =>
    match a,b with
    | .observation p1         , .observation p2           => p1 = p2
    | .observation p1         , .knot p2 _ _              => p1 = p2
    | .observation p1         , .interpolant p2 _ _ _ _   => p1 = p2.truth

    | .knot p1 _ _            , .observation p2           => p1 ≠ p2
    | .knot p1 poly1 sp1      , .knot p2 poly2 sp2        => (p1 = p2 ∧ poly1 ≤ poly2 ∧ sp1 ≤ sp2) ∨
                                                             (p1 ≠ p2 ∧ poly2 ≤ poly1 ∧ sp2 ≤ sp1)
    | .knot p1 _ _            , .interpolant p2 _ _ _ _   => p1 = p2.truth

    | .interpolant p1 _ _ _ _ , .observation p2           => p1.truth = p2
    | .interpolant p1 _ _ _ _ , .knot p2 _ _              => p1.truth = p2
    | .interpolant p1 _ _ _ _ , .interpolant p2 _ _ _ _   => p1 = p2


inductive Diatribe  -- 147
  | religion: Prop → Diatribe
  | speculation: Prop → Spline → Diatribe → Diatribe
  | rant: Prop → Spline → Diatribe → Diatribe → Diatribe

structure CrusadeProcess   -- Bullshit meter 3804
    (Value: Type i)
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
  where
  pwn_n00bz: ArmWaveProcess Value Carrier
  religion: Diatribe

  gate_keep? : Diatribe → Diatribe := fun d =>
    match d with
    | .religion prop => .religion prop
    | .speculation prop s _ => .speculation prop s religion
    | .rant prop s d1 _ => .rant prop s d1 religion

def CrusadeProcess.default
    (Value: Type i)
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
    : CrusadeProcess Value Carrier where
  pwn_n00bz :=
  { galerkin_process := matter.galerkin_process
    guess := .observation Fact.Truth.truth
  }
  religion := .religion Fact.Truth.truth

class PROPAGANDA  -- 3151
    (Value: Type i)
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
  where
  insinuation: CrusadeProcess Value Carrier
  -- What color (lol) is your pill?  Same color as your jar?
  red_pilled? : Diatribe → Prop := fun d =>
    match d with
    | .religion prop => prop
    | .speculation prop _ _ => prop
    | .rant prop _ _ _ => prop

inductive Cult  -- 6460
  | inside_joke: Prop → Cult
  | pythagoras: Prop → Diatribe → Cult → Cult
  | triangles: Prop → Diatribe → Fact → Cult → Cult → Cult

structure InitiationProcess  -- Bullshit meter ≈ 9117.   TBF, when is an initiation process not a bunch of bullshit?
    (Value: Type i)
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
  where
  -- Aristotle was a bugger for the bottle!
  ethos: CrusadeProcess Value Carrier
  sacred_texts: Cult
  initiate: Cult → Cult := fun c =>
    match c with
    | .inside_joke prop => .pythagoras prop space.insinuation.religion sacred_texts
    | .pythagoras prop crusade witness => .triangles d.fact.truth crusade d.fact witness (.inside_joke prop)
    | .triangles prop crusade fact witness event => .triangles prop crusade fact witness event

def InitiationProcess.default
    (Value: Type i)
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
    : InitiationProcess Value Carrier where
  ethos := CrusadeProcess.default Value Carrier
  sacred_texts := .inside_joke Fact.Truth.truth

class ACOLYTE   -- 7699
    (Value: Type i)
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
  where
  euclid : InitiationProcess Value Carrier
  judgement_day? : Cult → Prop := fun c =>
    match c with
    | .inside_joke prop => prop
    | .pythagoras prop _ _ => prop
    | .triangles prop _ _ _ _ => prop


end Measurement
