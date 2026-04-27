/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

-/

-- WE GET SIGNAL!
import Measurement.Episode6
set_option allowUnsafeReducibility true


-- MAIN SCREEN TURN ON
namespace Measurement

@[reducible]
structure ArmWaveProcess   -- 3306
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
  where
  galerkin_process : GalerkinProcess Value Carrier
  guess: Spline

  reticulate?: Spline → Spline := fun input =>
    match input with
    | .observation prop => .knot prop matter.galerkin_process.polynomial (.observation prop)
    | .knot prop poly _ => .knot prop poly guess
    | .interpolant prop poly prior _ => .interpolant prop poly prior guess

class BULLSHIT  -- 2733              Bullshit is __STRICTLY__ conserved.
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
  where
  arm_wave_process : ArmWaveProcess Value Carrier
  interpolate? : Spline → Spline → Prop := fun a b =>
    match a,b with
    | .observation p1         , .observation p2           => p1 = p2
    | .observation p1         , .knot p2 _ _              => p1 = p2
    | .observation p1         , .interpolant p2 _ _ _     => p1 = p2

    | .knot p1 _ _            , .observation p2           => p1 ≠ p2
    | .knot p1 poly1 sp1      , .knot p2 poly2 sp2        => (p1 = p2 ∧ poly1 ≤ poly2 ∧ sp1 ≤ sp2) ∨
                                                             (p1 ≠ p2 ∧ poly2 ≤ poly1 ∧ sp2 ≤ sp1)
    | .knot p1         , .interpolant p2 _ _ _     => p1 = p2

    | .knot prop _ _ => prop
    | .interpolant prop _ _ _ => prop.truth

inductive Diatribe  -- 147
  | religion: Prop → Diatribe
  | speculation: Prop → Spline → Diatribe → Diatribe
  | rant: Prop → Spline → Diatribe → Diatribe → Diatribe

structure CrusadeProcess   -- Bullshit meter 3804
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
  where
  pwn_n00bz: ArmWaveProcess Value Carrier
  religion: Diatribe

  gate_keep? : Diatribe → Diatribe := fun d =>
    match d with
    | .religion prop => .religion prop
    | .speculation prop s _ => .speculation prop s religion
    | .rant prop s d1 _ => .rant prop s d1 religion

class PROPAGANDA  -- 3151
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
  where
  -- Aristotle was a bugger for the bottle!
  ethos: CrusadeProcess Value Carrier
  sacred_texts: Cult
  initiate: Cult → Cult := fun c =>
    match c with
    | .inside_joke prop => .pythagoras prop space.insinuation.religion sacred_texts
    | .pythagoras prop crusade witness => .triangles d.fact.truth crusade d.fact witness (.inside_joke prop)
    | .triangles prop crusade fact witness event => .triangles prop crusade fact witness event

class ACOLYTE   -- 7699
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
  where
  euclid : InitiationProcess Value Carrier
  judgement_day? : Cult → Prop := fun c =>
    match c with
    | .inside_joke prop => prop
    | .pythagoras prop _ _ => prop
    | .triangles prop _ _ _ _ => prop


 end Measurement
