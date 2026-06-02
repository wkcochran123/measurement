


import Measurement.Episode9
-- Told you Chaitin gets expensive
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true
set_option maxRecDepth 100

namespace Measurement

universe i

@[reducible]
class WITNESSED
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
  where
  baptism: ReligiousProcess Value Carrier
  witness: Gospel

  risen? : Gospel → Gospel → Prop := fun a b =>
    Gospel.le a b → Gospel.le b a

instance WITNESSED_TRUTH
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    : WITNESSED Value Carrier where
  baptism :=
  { scientific_process := gospel.scientific_process
    the_literature := .epiphany d.fact.truth
  }
  witness := .epiphany d.fact.truth

inductive Truth
  | logic: Prop → Truth
  | fact: Gospel → Prop → Truth → Truth

namespace Truth
def le : Truth → Truth → Prop
  | .logic p1, .logic p2 => p1 = p2
  | .logic p1, .fact _ p2 _ => p1 = p2
  | .fact _ p1 _, .logic p2 => p1 ≠ p2
  | .fact g1 p1 t1, .fact g2 p2 t2 =>
    (Gospel.le g1 g2 ∧ p1 = p2 ∧ le t1 t2) ∨ le (.fact g1 p1 t1) t2
termination_by _ t => sizeOf t
end Truth

--  We have learned this through Quantum Eletrodynamics.
--  Damn, there's that fade away three nothing but net over __GODEL__ __COHEN__ __CANTOR__ __HILBERT__ and ...
--  No...  Without them, I would have stepped on the land mines.  It is _BECAUSE_ of them that I can see the land mines
--  and avoid them.
@[reducible]
structure UniverseTensor
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
  where
  frame_of_reference: ReligiousProcess Value Carrier
  reality: Truth

  -- Your _PUNY_ __GODS__ _ignore_ your pleas!
  -- The universe __SIMPLY__ dngaf!
  observe? : Truth → Truth := fun gospel =>
    match gospel with
    | .logic prop => .fact account.witness prop reality
    | .fact knowledge prop _ => .fact knowledge prop reality

@[reducible]
class REAL
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
  where
  universal_observer: UniverseTensor Value Carrier  -- Praise be to the universal observer.
  current_status: Truth

  metaphysical? : Truth → Truth → Prop := fun a b =>
    Truth.le a b → Truth.le b a

instance REAL_WITNESSED
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
    : REAL Value Carrier where
  universal_observer :=
  { frame_of_reference := account.baptism
    reality := .logic d.fact.truth
  }
  current_status := .fact account.witness d.fact.truth (.logic d.fact.truth)

inductive Variation
  | newton: Gospel → Prop → Variation
--      +-----    We do what we must because we can.
--      |
--      V
  | gateaux: Gospel → Prop → Prop → Variation → Variation      -- CAKE!
  | frechet: Gospel → Prop → Prop → Prop → Variation → Variation → Variation

namespace Variation
def le : Variation → Variation → Prop
  | .newton g1 p1, .newton g2 p2 =>
    Gospel.le g1 g2 ∧ p1 = p2
  | .newton g1 p1, .gateaux g2 _ p2 _ =>
    Gospel.le g1 g2 ∧ p1 = p2
  | .newton g1 p1, .frechet g2 _ p2 _ _ _ =>
    Gospel.le g1 g2 ∧ p1 = p2
  | .gateaux _ _ p1 _, .newton _ p2 =>
    p1 ≠ p2
  | .gateaux g1 a1 b1 v1, .gateaux g2 a2 b2 v2 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 = b2 ∧ le v1 v2) ∨
      le (.gateaux g1 a1 b1 v1) v2
  | .gateaux g1 a1 b1 v1, .frechet g2 a2 b2 _ v2 v3 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 = b2 ∧ (le v1 v2 ∨ le v1 v3)) ∨
      le (.gateaux g1 a1 b1 v1) v2 ∨ le (.gateaux g1 a1 b1 v1) v3
  | .frechet _ _ p1 _ _ _, .newton _ p2 =>
    p1 ≠ p2
  | .frechet g1 a1 b1 _ v1 v2, .gateaux g2 a2 b2 v3 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 ≠ b2 ∧ (le v1 v3 ∨ le v2 v3)) ∨
      le (.frechet g1 a1 b1 (a1 ∧ ¬b1) v1 v2) v3
  | .frechet g1 a1 b1 c1 v1 v2, .frechet g2 a2 b2 c2 v3 v4 =>
    (Gospel.le g1 g2 ∧ a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧
      ((le v1 v3 ∧ le v2 v4) ∨ (le v1 v4 ∧ le v2 v3))) ∨
      le (.frechet g1 a1 b1 c1 v1 v2) v3 ∨
        le (.frechet g1 a1 b1 c1 v1 v2) v4
termination_by _ v => sizeOf v
end Variation

@[reducible]
structure BigRedDogProcess
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
    [real: REAL Value Carrier]
  where
  universal_observer: UniverseTensor Value Carrier  -- Praise be to the universal observer.
  differential_equation: Variation
  transmute: Variation → Variation := fun variation =>
    match variation with
    | .newton g p => .gateaux g d.fact.truth p differential_equation
    | .gateaux g a b v =>
        -- Gateaux → Fréchet: add the residue.
        -- a is the direction, b is the response, a≠b is the strain.
        .frechet g a b (a ∧ ¬b) v differential_equation   -- the residue is exactly the informational strain
    | .frechet g a b c f1 _ =>
        -- Fréchet → Gateaux: project out the residue, collapse to direction only.
        -- This is the weak form. You lose the residue. That's the price of Galerkin.
        .gateaux g (d.fact.truth∧a) (b=c) f1

@[reducible]
class LOCAL
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
    [real: REAL Value Carrier]
  where
  theory: BigRedDogProcess Value Carrier
  delta: Prop
  experience: Variation → Variation → Prop := fun a b =>
    Variation.le a b

instance LOCAL_REAL
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
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
    [real: REAL Value Carrier]
    : LOCAL Value Carrier where
  theory :=
  { universal_observer := real.universal_observer
    differential_equation := .newton account.witness d.fact.truth
  }
  delta := d.fact.truth

end Measurement
