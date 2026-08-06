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
    [DISTINGUISHABLE Value Carrier]
    [ADMISSIBLE Value Carrier]
    [COUNTABLE Value Carrier]
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


inductive Science  -- 8029
  | repeatable: Prop → Science
  | hypothesis: Prop → Cult → Science
  | theory: Prop → Cult → Fact → Science → Science

structure LearningProcess  -- 26691
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
  where
  initiation_process : InitiationProcess Value Carrier
  -- Learn the ways of Galileo
  galileo: Cult
  -- In order to _DESCRIBE_ science.
  invariant: Science

  touch_stove? : Science → Science := fun s =>
    match s with
    | .repeatable propose => .hypothesis propose galileo
    | .hypothesis propose idea => .theory propose idea d.fact (.hypothesis propose galileo)
    | .theory propose prior fact _ => .theory propose prior fact invariant

def LearningProcess.default
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
    : LearningProcess Value Carrier where
  initiation_process := InitiationProcess.default Value Carrier
  galileo := .inside_joke Fact.Truth.truth
  invariant := .repeatable Fact.Truth.truth

class SCIENTIFIC -- 23964
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
  where
  phd_process : LearningProcess Value Carrier
  invariant: Science

  predictable? : Science → Science → Prop := fun a b =>
    match a, b with
    | _, .repeatable prop => prop
    | _, .hypothesis prop _ => prop
    | _, .theory prop _ _ _  => prop




inductive Knowledge  -- Bullshit meter 84
| jarjar: Prop → Knowledge
| ledger: Prop → Fact → Knowledge → Knowledge

namespace Knowledge   -- 424
def le : Knowledge → Knowledge → Prop
  | .jarjar f1, .jarjar f2 => f1 = f2
  | .jarjar _, _ => True
  | _, .jarjar _=> False
  | .ledger f1 p1 k1, .ledger f2 p2 k2 =>
    (f1 = f2 ∧ p1 = p2 ∧ le k1 k2) ∨ le (.ledger f1 p1 k1) k2
termination_by _ k => sizeOf k
end Knowledge

@[reducible] -- We have learned this in the learning process
-- lol.  10 years of learning about the Taylor series.  It's like I can manipulate them with my eyes closed now.
structure ScientificProcess  -- 104499
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
  where
  learning_process: LearningProcess Value Carrier
  knowledge: Knowledge

  learn? : Knowledge → Knowledge := fun know =>
    match know with
    | .jarjar p       => .ledger p d.fact knowledge
    |.ledger p f _   => .ledger p f knowledge

class TRUTH  -- 5632
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
  where
  scientific_process: ScientificProcess Value Carrier
  martyred? : Knowledge → Knowledge → Prop := fun f1 f2 =>
    Knowledge.le f1 f2 → Knowledge.le f2 f1



inductive Gospel  -- 67
  | epiphany: Prop → Gospel
  | state: Knowledge → Prop → Gospel → Gospel

namespace Gospel
def le : Gospel → Gospel → Prop
  | .epiphany p1, .epiphany p2 => p1 = p2
  | .epiphany p1, .state _ p2 _ => p1 = p2
  | .state _ p1 _, .epiphany p2 => p1 ≠ p2
  | .state f1 p1 g1, .state f2 p2 g2 =>
    (Knowledge.le f1 f2 ∧ p1 = p2 ∧ le g1 g2) ∨ le (.state f1 p1 g1) g2
termination_by _ g => sizeOf g
end Gospel

@[reducible] -- We have learned this while watching others.
structure ReligiousProcess
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
  scientific_process: ScientificProcess Value Carrier
  the_literature: Gospel

  pray? : Gospel → Gospel := fun prayer =>
    match prayer with
    | .epiphany prop => .state gospel.scientific_process.knowledge prop the_literature
    | .state _ prop experiment => .state gospel.scientific_process.knowledge prop experiment

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
    [real: REAL Value Carrier]    -- The idea that a real number can be reperesented isn't real.
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
    [imaginary: REAL Value Carrier]
    (real: REAL Value Carrier)
  where
  theory: BigRedDogProcess Value Carrier
  delta: Prop
  experience: Variation → Variation → Prop := fun a b =>
    Variation.le a b


inductive SpaceTimePath
  | einstein: Fact → SpaceTimePath
  | white_hole: Fact → Type i → SpaceTimePath → SpaceTimePath
  | blackhole: Prop → Type (i+1) → SpaceTimePath → SpaceTimePath
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
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier]
    (imaginary: REAL Value Carrier)
  where
  derivative: BigRedDogProcess Value Carrier  -- Parents, read to your kids.  They are the future.
  function: SpaceTimePath
  converged: Fact
  sink: Type (i+1)

  photon_torpedo: SpaceTimePath → SpaceTimePath := fun path =>
    match path with
    | .einstein fact =>
                .white_hole converged Value (.einstein fact)
    | .white_hole fact val path =>
              match fact.decTruth with
              | isTrue _ =>
                    .geodesic d.fact val d.fact.truth (ULift.{i+1} val) path function
              | isFalse _ =>
                    .blackhole fact.truth (ULift.{i+1} val) function
    | .geodesic fact val1 prop val2 _ _ =>
              match fact.decTruth with
              | isTrue _ =>
                    .geodesic d.fact
                              val1
                              prop
                              val2
                              (.white_hole converged (ULift.{i} Value) (.einstein fact))
                              (.einstein fact)
              | isFalse _ =>
                    .blackhole fact.truth sink function
    | .blackhole prop val after => .blackhole prop val after


@[reducible]
class UNIVERSAL
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier]
  where
  the_compiler: CalculusProcess Value Carrier real -- Praise be to the universal compiler.
  source_program: SpaceTimePath
  compiled_program: SpaceTimePath

  -- let's ask the compiler to hold the quarter we glued to the table.
  lake_build: SpaceTimePath → SpaceTimePath → Prop := fun _ _ => the_compiler.converged = d.fact



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
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier]
    (imaginary: REAL Value Carrier)
    (computer_science: UNIVERSAL Value Carrier)
  where
  bullshit_meter: CalculusProcess Value Carrier real -- Praise be to the heart.
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


@[reducible]
class LOGICAL
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [imaginary: REAL Value Carrier]
    [delta: UNIVERSAL Value Carrier]
  where
  feelings: HeartbeatProcess Value Carrier imaginary delta
  ekg: Calibration.EKG

  logical? : YarnTheory → YarnTheory → Prop := fun a b =>
    YarnTheory.le a b


namespace ComputerProgram
def le
    (Value : Type i)
    (Carrier : CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    : ComputerProgram → ComputerProgram → Prop
  | .boolean p1 p2 p3 t1 t2 t3 program1,
      .boolean p4 p5 p6 t4 t5 t6 program2 =>
    let before := ComputerProgram.boolean p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.boolean p4 p5 p6 t4 t5 t6 program2
    prop.ekg.booleanProgram? before after
  | .transform p1 p2 t1 t2 program1,
      .boolean p3 p4 p5 t3 t4 t5 program2 =>
    let before := ComputerProgram.transform p1 p2 t1 t2 program1
    let after := ComputerProgram.boolean p3 p4 p5 t3 t4 t5 program2
    prop.ekg.transformBoolean? before after
  | .boolean p1 p2 p3 t1 t2 t3 program1,
      .transform p4 p5 t4 t5 program2 =>
    let before := ComputerProgram.boolean p1 p2 p3 t1 t2 t3 program1
    let after := ComputerProgram.transform p4 p5 t4 t5 program2
    prop.ekg.booleanTransform? before after
  | _, _ => False
end ComputerProgram

@[reducible]
structure ElaborationProcess
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [LOCAL Value Carrier real] (imaginary: REAL Value Carrier)
    [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
  where
  stamina: HeartbeatProcess Value Carrier imaginary delta
  calibration: Calibration.EKG
  computer_state:  ComputerProgram

  execute: ComputerProgram → ComputerProgram := fun op_code =>
      match op_code with
      | .load load_prop load_type =>
                  .transform load_prop (¬load_prop) load_type (ULift.{i+1} Value)
                    (.load load_prop load_type)
      | .transform p1 p2 t t1 program =>
                  .boolean p1 p2 d.fact.truth t t1 (ULift.{i+1} t1) program

      | .boolean outer_p1 outer_p2 outer_p3 outer_t _ outer_ti outer_program =>
                    if calibration.outgrown? op_code then
                      .load (¬outer_p1 ∧ ¬outer_p2 ∧ outer_p3) outer_t
                    else
                      match d.fact.decTruth with
                        | isTrue _  => .boolean outer_p2 outer_p3 d.fact.truth
                                          outer_t (ULift.{i+1} outer_t) outer_ti outer_program
                        | isFalse _ => .load (¬outer_p1 ∧ ¬outer_p2 ∧ outer_p3) outer_t




@[reducible]
class HALTED
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
  where
  scientific_paper: ElaborationProcess Value Carrier real

  halted? : ComputerProgram → ComputerProgram → Prop := fun _ program =>
    match program with
    | .load p _ => p
    | .transform p _ _ _ _ => p
    | .boolean p _ _ _ _ _ _ => p


inductive Measurement
|origin: Fact → Number → Type i → Measurement
|distance: Fact → Number → Number → Type i → Type (i+1) → Measurement → Measurement
|speed: Fact → Number → Number → Number → Type i → Type (i+1) → Type i →  Measurement → Measurement → Measurement

namespace Measurement
def le : Measurement → Measurement → Prop := fun t1 t2 =>
  match t1, t2 with
  | .origin f1 num1 _, origin f2 num2 _ => (f1 = f2) ∧ num1 ≤ num2
  | .origin _ _ _ , _ => True
  | _ , .origin _ _ _ => False
  | .distance f1 _ length1 _ _ _, .distance f2 _ length2 _ _ _ => (f1 = f2) ∧ length1 ≤ length2
  | .distance _ _ _ _ _ _, _ => True
  | _, .distance _ _ _ _ _ _ => False
  | .speed f1 _ _ speed1 _ _ _ _ _ , .speed f2 _ _ speed2 _ _ _ _ _ => (f1 = f2) ∧ speed1 ≤ speed2
end Measurement

instance : LE Measurement where
  le := Measurement.le

@[reducible]
structure LeanProcess
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    [executable: HALTED Value Carrier]
  where
  description: ElaborationProcess Value Carrier real
  length: Number
  velocity: Measurement
  projection: Type i


  evolve? : Measurement → Measurement := fun x =>
    match x with
    | .origin fact number _ => .distance fact number length Value (ULift.{i+1} Value) velocity
    | .distance fact x1 x2 _ _ v =>
                                .speed fact x1 x2 length Value (ULift.{i+1} Value) projection v velocity
    | .speed fact _ x2 x3 _ _ _ _ v =>
                                .speed fact x2 x3 length Value (ULift.{i+1} Value) projection v velocity


@[reducible]
class MEASURED
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier]
    [executable: HALTED Value Carrier]
  where
  satire: LeanProcess Value Carrier real

  bounded? := fun a b => Measurement.le a b

/-
HOUSE-TAPE CHORUS, STANZA 2 -- DRAFT PANEL TEXT

This is the compiler
that emitted the tape
that lived in the Fact
that John built.

It does not emit the story.  It emits the small object the story must
walk around.  The reader sees a house; the machine sees a character on
a tape and the local permissions that let it move.
-/
@[reducible]
structure CompilerOutput
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
  where
  satire: LeanProcess Value Carrier real
  tape: CompilerTape

  emit?: CompilerTape → CompilerTape := fun t =>
    match t with
    | .boot a b                => .strap a d.fact b (ULift.{i+1, i} b) tape
    | .strap f1 f2 t t1 symbol => .compute f1 f2 d.fact.truth t t1 (ULift.{i+1, i+1} t1) symbol
    | .compute f1 f2 _ t t1 t2 remainder =>
          match f1.decTruth,f2.decTruth with
          | isTrue _     , isTrue _    =>  .boot Fact.Truth Value
          | isTrue _     , isFalse _   =>  .compute f1 d.fact d.fact.truth t t1 t2 remainder
          | isFalse _    , isTrue _    =>  .compute d.fact f2 d.fact.truth t t1 t2 remainder
          | isFalse _    , isFalse _   =>  .strap Fact.Truth Fact.Truth t t1 remainder

/-
HOUSE-TAPE CHORUS, STANZA 1 -- DRAFT PANEL TEXT

This is the tape
that lived in the Fact
that John built.

The tape is one character.  Not a sentence, not a proof, not a world.
The house grows around it because every later reader wants to know what
that one character was allowed to mean.
-/
inductive CompilerTape where
  | boot    : Fact → Type i → CompilerTape
  | strap   : Fact → Fact → Type i → Type (i+1) → CompilerTape → CompilerTape
  | compute : Fact → Fact → Prop → Type i → Type (i+1) → Type (i+1) → CompilerTape → CompilerTape

namespace CompilerTape
def le : CompilerTape → CompilerTape → Prop := fun t1 t2 =>
  match t1, t2 with
  | .boot _ _         , _                 => True
  | _                   , .boot _ _       => False
  | .strap f1 _ _ _ _   , .strap f2 _ _ _ _ => f1 = f2
  | _                   , .strap _ _ _ _ _  => False
  | .strap _ _ _ _ _    , _                 => True
  | .compute f1 f2 _ _ _ _ _ , .compute f3 f4 _ _ _ _ _ => (f1 = f3) ∧ (f2 ≠ f4)

def lt : CompilerTape → CompilerTape → Prop := fun n1 n2 => le n1 n2 ∧ ¬ le n2 n1

end CompilerTape

instance : LE CompilerTape where
  le := CompilerTape.le
instance : LT CompilerTape where
  lt := CompilerTape.lt

/-
HOUSE-TAPE CHORUS, STANZA 3 -- DRAFT PANEL TEXT

This is the object file
that carried the compiler
that emitted the tape
that lived in the Fact
that John built.

Compilation is not an explanation.  It is the paperwork that lets the
one-character tape become a thing the next panel may legally read.
Four is off a ways in instances.
-/
@[reducible]
class COMPILED
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [real: REAL Value Carrier] [epsilon: LOCAL Value Carrier real] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier real]
  where
  compiler_output: CompilerOutput Value Carrier real
  object_file: CompilerTape

  converged?: CompilerTape → CompilerTape → Prop := fun a b => a < b

inductive Bullshit where
| zero  : Fact → Bullshit
| one   : Fact → Number → CompilerTape → CompilerTape → Bullshit → Bullshit
| rest  : Fact → Fact → Prop → Number → Number → Number → CompilerTape → CompilerTape →
                    Bullshit → Bullshit → Bullshit

namespace Bullshit
  def le : Bullshit → Bullshit → Prop
  | .zero f                    , .zero g                    => f.truth = g.truth
  | .zero _                    , _                          => True  -- Zero is the origin for all

  | .one _ _ _ _ _             , .zero _                    => False
  | .one p1 n1' _ _ _          , .one p2 n2' _ _ _          =>
                                                    match p1.decTruth, p2.decTruth with
                                                    | isTrue _,  isTrue _  => n1' ≤ n2'
                                                    | isFalse _, isFalse _ => n2' ≤ n1'
                                                    | isTrue _,  isFalse _ => False
                                                    | isFalse _, isTrue _  => True
  | .one _ _ _ _ _             , .rest _ _ _ _ _ _ _ _ _ _  => True

  | .rest _ _ _ _ _ _ _ _ _ _  , .zero _                    => False
  | .rest _ _ _ _ _ _ _ _ _ _  , .one _ _ _ _ _             => False

  | .rest f1 g1 p1 _ _ n13 _ _ m11 m12,
  .rest f2 g2 p2 _ _ n23 _ _ m21 m22 =>
    (f1.truth = f2.truth) ∧
    (g1.truth = g2.truth) ∧
    (p1 -> p2) ∧
    (n13 ≤ n23) ∧
    le m11 m21 ∧
    le m12 m22

def lt: Bullshit → Bullshit → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Bullshit

instance : LE Bullshit where
  le := Bullshit.le
instance : LT Bullshit where
  lt := Bullshit.lt


structure AtreyuProcess
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier] where
  compiler_output: CompilerOutput Value Carrier imaginary
  next_measurement: Bullshit
  stress: Number
  strain: Number := Carrier.event Carrier.value   -- Delicious Ouroboros!!
  proof: CompilerTape


  satirize: Bullshit → Bullshit := fun measurement =>
  match measurement with
  |.zero _    =>
              .one d.fact stress proof compiler_output.tape next_measurement
  |.one fact last_stress last_object last_state last_measurement =>
              match fact.decTruth, d.fact.decTruth with
              | isTrue _,  isTrue _  =>
                  .rest fact d.fact
                    ((fact.truth = d.fact.truth ∧ last_stress ≤ stress) ∨
                    (fact.truth ≠ d.fact.truth ∧ stress ≤ last_stress))
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isTrue _,  isFalse _ =>
                  .rest fact d.fact
                    False
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isFalse _, isTrue _  =>
                  .rest fact d.fact
                    True
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isFalse _, isFalse _ =>
                  .rest fact d.fact
                    ((fact.truth = d.fact.truth ∧ stress ≤ last_stress) ∨
                    (fact.truth ≠ d.fact.truth ∧ last_stress ≤ stress))
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

  | .rest _ f2 _ _ n2 n3 _ prior_proof _ if_false =>
              match f2.decTruth, d.fact.decTruth with
              | isTrue _,  isTrue _  =>
                  .rest f2 d.fact
                    ((f2.truth = d.fact.truth ∧ n2 ≤ stress) ∨
                    (f2.truth ≠ d.fact.truth ∧ stress ≤ n2))
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isTrue _,  isFalse _ =>
                  .rest f2 d.fact
                    False
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isFalse _, isTrue _  =>
                  .rest f2 d.fact
                    True
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isFalse _, isFalse _ =>
                  .rest f2 d.fact
                    ((f2.truth = d.fact.truth ∧ stress ≤ n2) ∨
                    (f2.truth ≠ d.fact.truth ∧ n2 ≤ stress))
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement


  bilinear? : Bullshit → Bullshit → Bullshit := fun a b =>
    -- Back-to-back satirize: lift both inputs one rung, then hang them as the two
    -- children of a single .rest -- the only constructor that carries a pair.  The
    -- Prop slot holds the slip (sa < sb); residue? is exactly the projection of it.
    -- (satirize lifts every rung, so neither side is ever .zero -- the floor arms are
    -- kept only for totality and collapse to the surviving satire.)
    match satirize a, satirize b with
    | .zero _, sb      => sb
    | sa,      .zero _ => sa
    | sa,      sb      =>
        .rest d.fact d.fact (sa < sb)
              stress stress strain
              proof proof
              sa sb

  -- residue? is the PROJECTION of the operator: run bilinear?, then read the slip out of
  -- the .rest's Prop slot.  The only `none` is the commute -- both inputs at the origin
  -- floor -- mirroring how `.zero` floors Bullshit.le and `none` floors slipLe.  This is
  -- the option the residue computation (obfusplained?/close?) reads off.
  residue? : Bullshit → Bullshit → Option Prop := fun a b =>
    match a, b with
    | .zero _, .zero _ => none
    | _,       _       =>
        match bilinear? a b with
        | .rest _ _ p _ _ _ _ _ _ _ => some p
        | _                          => none




class TrueOutput
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
  where
  atreyu_process : AtreyuProcess Value Carrier imaginary
  TRUE : Bullshit := .zero d.fact
  -- output is the compiler/reader output: the THEORY rung of the bullshit
  -- ladder, NOT the origin TRUE.  Instances must supply it.
  output : Bullshit
  -- The certificate is now ORDERING, not equality: the .zero origin (TRUE)
  -- is the floor below the accumulated bullshit `output`.  `Bullshit.le` gives
  -- `.zero _ , _ => True` for ANY second argument, so `TRUE ≤ output` is the
  -- honest definitional witness no matter which rung `output` lands on.
  output_true : TRUE ≤ output
  raw_output : Bullshit := atreyu_process.satirize atreyu_process.next_measurement

  obfusplained? : TRUE ≤ output → Bullshit → Bullshit → Option Prop := fun _ a b =>
  match a, b with
  | .zero _, .zero _ => none            -- two origins: they commute, no slip
  | _,       _       => some (a < b)    -- a real rung pair: the slip, condition a < b

def You_the_Reader
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
 : AtreyuProcess Value Carrier imaginary where
  compiler_output := compiled.compiler_output
  next_measurement := .zero d.fact
  stress := Carrier.value
  proof := compiled.object_file

-- THEORY: the three pieces of bullshit as a named ladder, expressed as defs
-- (NOT a 34-binder structure -- a structure here forces a fresh 34-gate
-- instance synthesis at every use site, which is exactly the elaboration cost
-- we are fighting).  Each rung takes the reader-process explicitly and
-- satirizes the PREVIOUS rung, so the chain is well-founded and bottoms at the
-- .zero origin.  `THEORY.raw_output` is the HYPOTHESIS rung (.one): the compiler
-- output the device reads, NOT the origin TRUE.  (It is the b rung, one satirize
-- up; the theory rung c/.rest is still defined below for Episode16's
-- velocity/acceleration variations, but is not used as the certified output --
-- see the raw_output comment for why.)
namespace THEORY

variable {Value : Type i} {Carrier : CarrierProcess Value}
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]

def repeatable
    (_reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  origin                                                       -- piece 1: the origin / repeatable observation

def hypothesis
    (reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  reader.satirize (repeatable reader origin)                   -- piece 2: one step on the previous

def theory
    (reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  reader.satirize (hypothesis reader origin)                   -- piece 3: the accumulated rest

def raw_output
    (reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  hypothesis reader origin                                     -- the compiler output the device reads:
  -- the hypothesis rung (.one).  satirize(.zero) constructs `.one` with a
  -- STATIC head (no decTruth match), so `TRUE ≤ raw_output` certifies cheaply
  -- by `trivial`.  The theory rung (.rest) is the same ladder one step higher
  -- but its head is gated behind a stuck `decTruth` match, which makes the
  -- ordering certificate computationally pathological; the three rung defs
  -- (repeatable/hypothesis/theory) remain intact for the velocity/acceleration
  -- variations in Episode16.

end THEORY

instance TRUE_COMPILED
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    : TrueOutput Value Carrier imaginary where
  atreyu_process := You_the_Reader Value Carrier
  TRUE := .zero d.fact
  -- output is THEORY.raw_output: the hypothesis rung (.one) the reader-process
  -- produced by satirizing the .zero origin once.
  output := THEORY.raw_output (You_the_Reader Value Carrier) (.zero d.fact)
  -- TRUE (.zero) is the floor below that accumulated bullshit.  `output` is the
  -- hypothesis rung = satirize(.zero), which reduces to a `.one`-headed Bullshit
  -- with no stuck decTruth match, so `Bullshit.le .zero (.one ..)` reduces to
  -- `True` and `trivial` closes it cheaply.
  output_true := by trivial

instance DISTINGUISHABLE_PROP
    (Carrier : CarrierProcess Prop)
    : DISTINGUISHABLE Prop Carrier where
  fact := Carrier.symbol
  symbol := Prop
  different? := fun _ => True
  dec_distinct := fun _ => isTrue trivial



def truthCarrier : CarrierProcess Prop where
  symbol := Fact.Truth
  value := .zero Fact.Truth

instance truthDistinct :
    DISTINGUISHABLE Prop truthCarrier where
  fact := truthCarrier.symbol
  symbol := Prop
  different? := fun _ => True
  dec_distinct := fun _ => isTrue trivial


noncomputable instance COMPARABLE_PHYSICAL
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [electron: Inhabited d.symbol]
    : COMPARABLE Value Carrier where
  physical_process :=
  { physical_process := cc.noisy_process
    representation := default
    invariant := .base d.fact default
    value := .base d.fact (ULift.up default)
  }
  smaller_than := fun m1 m2 => m1 = m2


/-- The truth order on the bullshit ladder -- the relation the needle collapses.
`@[reducible]` so it unfolds to `≤` under unification (e.g. against `output_true`). -/
@[reducible] def TruthOrder (a b : Bullshit) : Prop := a ≤ b

/-- THE NEEDLE: the single sanctioned `Quot.sound` site.  Two readings that are
ordered on the truth ladder collapse to the same truth-phase class.  Raw `Quot`,
no `Setoid` (no refl/symm/trans obligation) -- so `#print axioms selection_sound`
is exactly `[Quot.sound]`.  The genuinely-undecidable "are these the same truth?"
is never DECIDED (no `Classical.propDecidable`) and never FLATTENED (no `fun _ =>
True`): related readings are IDENTIFIED by one quotient soundness. -/
theorem selection_sound {α : Sort _} {r : α → α → Prop} {a b : α}
    (h : r a b) : Quot.mk r a = Quot.mk r b :=
  Quot.sound h


namespace Fact

noncomputable def SAME
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier imaginary]
    : Fact :=
  -- The needle, honest.  "TRUE and the output are the SAME truth" = the two
  -- readings collapse to one class in the truth-order quotient, witnessed by the
  -- one located `Quot.sound` (`selection_sound`), with the genuine ordering witness
  -- `out.output_true : TRUE ≤ output`.  No classical decision; no flattening.
  -- (`SAME.truth` is only ever compared reflexively in `Closure.le` -- every chair
  -- closure uses this same `Fact.SAME`, so `f1.truth = f2.truth` stays `X = X`.)
  { truth := Quot.mk TruthOrder out.TRUE = Quot.mk TruthOrder out.output
    decTruth := Decidable.isTrue (selection_sound (r := TruthOrder) out.output_true) }

end Fact

inductive Closure
  | same : Fact → Bullshit → Closure
  | different : Fact → Bullshit → Bullshit → Option Prop → Closure
  | inferred : Fact → Fact → Bullshit → Bullshit → Option Prop → Closure → Closure

namespace Closure

/-- The slip order on a node's commutator slot.  `none` (the operators commuted -- no slip) is the
floor, mirroring how `.zero` floors `Bullshit.le`; between two genuine slips the original Prop
implication survives. -/
def slipLe : Option Prop → Option Prop → Prop
  | none,   _      => True
  | some _, none   => False
  | some p, some q => p → q

/-- Slip composition (the cocycle the coherence checks compare against).  `none` is the identity --
a commuting step contributes nothing -- and two genuine slips compose by conjunction. -/
def slipAnd : Option Prop → Option Prop → Option Prop
  | none,   y      => y
  | x,      none   => x
  | some p, some q => some (p ∧ q)

def le : Closure → Closure → Prop
  | .same f1 b1, .same f2 b2 =>
      f1.truth = f2.truth ∧ b1 ≤ b2

  | .same f1 b1, .different f2 a2 b2 _ =>
      f1.truth = f2.truth ∧ (b1 ≤ a2 ∨ b1 ≤ b2)

  | .same f1 b1, .inferred f2 f3 a2 b2 _ prior =>
      (f1.truth = f2.truth ∨ f1.truth = f3.truth) ∧
        (b1 ≤ a2 ∨ b1 ≤ b2) ∨ le (.same f1 b1) prior

  | .different f1 a1 b1 _, .same f2 b2 =>
      f1.truth ≠ f2.truth ∨ ¬ (a1 ≤ b2 ∨ b1 ≤ b2)

  | .different f1 a1 b1 rel1, .different f2 a2 b2 rel2 =>
      f1.truth = f2.truth ∧ a1 ≤ a2 ∧ b1 ≤ b2 ∧ slipLe rel1 rel2

  | .different f1 a1 b1 rel1, .inferred f2 f3 a2 b2 rel2 prior =>
      ((f1.truth = f2.truth ∨ f1.truth = f3.truth) ∧
        a1 ≤ a2 ∧ b1 ≤ b2 ∧ slipLe rel1 rel2) ∨
          le (.different f1 a1 b1 rel1) prior

  | .inferred f1 f2 a1 b1 _ _, .same f3 b3 =>
      (f1.truth ≠ f3.truth ∧ f2.truth ≠ f3.truth) ∨
        ¬ (a1 ≤ b3 ∨ b1 ≤ b3)

  | .inferred f1 f2 a1 b1 rel1 prior1, .different f3 a3 b3 rel3 =>
      ((f1.truth = f3.truth ∨ f2.truth = f3.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ slipLe rel1 rel3) ∨
          le prior1 (.different f3 a3 b3 rel3)

  | .inferred f1 f2 a1 b1 rel1 prior1,
    .inferred f3 f4 a3 b3 rel3 prior2 =>
      ((f1.truth = f3.truth ∨ f2.truth = f4.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ slipLe rel1 rel3 ∧ le prior1 prior2) ∨
          le (.inferred f1 f2 a1 b1 rel1 prior1) prior2
termination_by c1 c2 => sizeOf c1 + sizeOf c2

end Closure


@[reducible]
structure EquivalenceProcess
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier imaginary]
  where
  atreyu_process : AtreyuProcess Value Carrier imaginary
  closure : Closure

  close? : Bullshit → Bullshit → Closure := fun a b =>
    .different (Fact.SAME Value Carrier) a b (out.obfusplained? out.output_true a b)

set_option trace.profiler true
-- The following were dropped after the device/out diagnosis. They produced
-- a flood that the library-suggestions pass (SymbolFrequency, SineQuaNon)
-- could not finish under `whnf` heartbeats. Re-enable locally with
-- `set_option ... in ...` around the specific subterm being investigated.
-- set_option trace.Meta.synthInstance true
-- set_option synthInstance.maxHeartbeats 20000
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.whnf true

@[reducible]
class INFERRED
    (Value: Type i)
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
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier imaginary]
  where
  equivalence_process : EquivalenceProcess Value Carrier
  theory : Closure

  inferred? : Closure → Closure → Prop := fun a b =>
    Closure.le a b

end Measurement
