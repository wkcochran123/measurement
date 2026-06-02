/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

-/


import Measurement.Episode8
-- Told you Chaitin gets expensive
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true

namespace Measurement

universe i

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


instance SCIENTIFIC_ACOLYTE
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
    [dd: COMPARABLE Value Carrier]
    [ee: OBSERVED Value Carrier]
    [ff: PRESENT Value Carrier]
    [gg: MEASURABLE Value Carrier]
    [hh: GUNGAN Value Carrier]
    [ii: SOURCE Value Carrier]
    [jj: EXECUTED Value Carrier]
    [kk: VALUE Value Carrier]
    [ll: MAGNITUDE Value Carrier]
    [mm: SCALED Value Carrier]
    [nn: LOAD Value Carrier]
    [oo: FINITE_ELEPHANT Value Carrier]
    [pp: BULLSHIT Value Carrier]
    [qq: PROPAGANDA Value Carrier]
    [rr: ACOLYTE Value Carrier]
    : SCIENTIFIC Value Carrier where
  phd_process := LearningProcess.default Value Carrier
  invariant := .hypothesis Fact.Truth.truth (.inside_joke Fact.Truth.truth)


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


instance TRUTH_SCIENTIFIC
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
    : TRUTH Value Carrier where
  scientific_process :=
  { learning_process := ideology.phd_process
    knowledge := .jarjar d.fact.truth
  }

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


end Measurement
