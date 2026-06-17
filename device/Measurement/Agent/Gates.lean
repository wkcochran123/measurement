/-
Measurement.Agent.Gates

The episode gate cascade as DATA, not as a 30+ instance-implicit binder
tower. `Gate` is one constructor per episode gate; `Gates` is one bundled
record of `GateEvidence`. No per-gate class, no projection instances (those
are reserved for a later production refactor, per the design spec).
-/
import Measurement.Agent.Core

set_option autoImplicit false

universe u

namespace Measurement.Agent

/-- One constructor per episode gate. Episode spellings are all-caps
(DISTINGUISHABLE, ..., LOCAL, ..., INFERRED); Lean constructors are lower
camel case. `localGate` maps to the episode `LOCAL` gate (`local` is a Lean
keyword). -/
inductive Gate where
  | distinguishable | admissible | countable | encoded | residue
  | binary | repeatable | numeric | representable | physical | comparable | observed
  | present | measurable | gungan | source | executed | value | magnitude | scaled | load
  | finiteElephant | bullshit | propaganda | acolyte
  | scientific | truth | witnessed | real | localGate | universal | logical | halted | measured | compiled
  | inferred
  deriving DecidableEq, Repr

namespace Gate

/-- Flat lookup rank, one arm per gate. No recursion, no search. -/
def rank : Gate → Nat
  | .distinguishable => 0
  | .admissible => 1
  | .countable => 2
  | .encoded => 3
  | .residue => 4
  | .binary => 5
  | .repeatable => 6
  | .numeric => 7
  | .representable => 8
  | .physical => 9
  | .comparable => 10
  | .observed => 11
  | .present => 12
  | .measurable => 13
  | .gungan => 14
  | .source => 15
  | .executed => 16
  | .value => 17
  | .magnitude => 18
  | .scaled => 19
  | .load => 20
  | .finiteElephant => 21
  | .bullshit => 22
  | .propaganda => 23
  | .acolyte => 24
  | .scientific => 25
  | .truth => 26
  | .witnessed => 27
  | .real => 28
  | .localGate => 29
  | .universal => 30
  | .logical => 31
  | .halted => 32
  | .measured => 33
  | .compiled => 34
  | .inferred => 35

/-- All gates in cascade order. -/
def all : List Gate :=
  [.distinguishable, .admissible, .countable, .encoded, .residue,
   .binary, .repeatable, .numeric, .representable, .physical, .comparable, .observed,
   .present, .measurable, .gungan, .source, .executed, .value, .magnitude, .scaled, .load,
   .finiteElephant, .bullshit, .propaganda, .acolyte,
   .scientific, .truth, .witnessed, .real, .localGate, .universal, .logical, .halted, .measured, .compiled,
   .inferred]

end Gate

/-- Per-gate evidence. All fields default; constructing one is `{}`. `name`
appears only in the `cost` default, `Value` only in the `carrier` type. -/
structure GateEvidence (name : Gate) (Value : Type u) (carrier : Carrier Value) where
  fact : Fact := carrier.symbol
  cost : Nat := Gate.rank name
  ok : Prop := True

/-- The whole gate cascade as one bundled record: one field per gate, each a
`GateEvidence`. This is the single object that replaces the 30+ binder tower
on the late episode classes. -/
structure Gates (Value : Type u) (carrier : Carrier Value) where
  distinguishable : GateEvidence .distinguishable Value carrier
  admissible : GateEvidence .admissible Value carrier
  countable : GateEvidence .countable Value carrier
  encoded : GateEvidence .encoded Value carrier
  residue : GateEvidence .residue Value carrier
  binary : GateEvidence .binary Value carrier
  repeatable : GateEvidence .repeatable Value carrier
  numeric : GateEvidence .numeric Value carrier
  representable : GateEvidence .representable Value carrier
  physical : GateEvidence .physical Value carrier
  comparable : GateEvidence .comparable Value carrier
  observed : GateEvidence .observed Value carrier
  present : GateEvidence .present Value carrier
  measurable : GateEvidence .measurable Value carrier
  gungan : GateEvidence .gungan Value carrier
  source : GateEvidence .source Value carrier
  executed : GateEvidence .executed Value carrier
  value : GateEvidence .value Value carrier
  magnitude : GateEvidence .magnitude Value carrier
  scaled : GateEvidence .scaled Value carrier
  load : GateEvidence .load Value carrier
  finiteElephant : GateEvidence .finiteElephant Value carrier
  bullshit : GateEvidence .bullshit Value carrier
  propaganda : GateEvidence .propaganda Value carrier
  acolyte : GateEvidence .acolyte Value carrier
  scientific : GateEvidence .scientific Value carrier
  truth : GateEvidence .truth Value carrier
  witnessed : GateEvidence .witnessed Value carrier
  real : GateEvidence .real Value carrier
  localGate : GateEvidence .localGate Value carrier
  universal : GateEvidence .universal Value carrier
  logical : GateEvidence .logical Value carrier
  halted : GateEvidence .halted Value carrier
  measured : GateEvidence .measured Value carrier
  compiled : GateEvidence .compiled Value carrier
  inferred : GateEvidence .inferred Value carrier

namespace Gates

/-- Dependent lookup by gate name. A plain function, not an instance. -/
def get {Value : Type u} {carrier : Carrier Value}
    (g : Gates Value carrier) : (name : Gate) → GateEvidence name Value carrier
  | .distinguishable => g.distinguishable
  | .admissible => g.admissible
  | .countable => g.countable
  | .encoded => g.encoded
  | .residue => g.residue
  | .binary => g.binary
  | .repeatable => g.repeatable
  | .numeric => g.numeric
  | .representable => g.representable
  | .physical => g.physical
  | .comparable => g.comparable
  | .observed => g.observed
  | .present => g.present
  | .measurable => g.measurable
  | .gungan => g.gungan
  | .source => g.source
  | .executed => g.executed
  | .value => g.value
  | .magnitude => g.magnitude
  | .scaled => g.scaled
  | .load => g.load
  | .finiteElephant => g.finiteElephant
  | .bullshit => g.bullshit
  | .propaganda => g.propaganda
  | .acolyte => g.acolyte
  | .scientific => g.scientific
  | .truth => g.truth
  | .witnessed => g.witnessed
  | .real => g.real
  | .localGate => g.localGate
  | .universal => g.universal
  | .logical => g.logical
  | .halted => g.halted
  | .measured => g.measured
  | .compiled => g.compiled
  | .inferred => g.inferred

/-- Build the whole bundle directly from a carrier. Every field is `{}`
(all-default `GateEvidence`). No `inferInstance` chain. -/
def default {Value : Type u} (carrier : Carrier Value) : Gates Value carrier :=
  { distinguishable := {}, admissible := {}, countable := {}, encoded := {}, residue := {}
  , binary := {}, repeatable := {}, numeric := {}, representable := {}, physical := {}
  , comparable := {}, observed := {}, present := {}, measurable := {}, gungan := {}
  , source := {}, executed := {}, value := {}, magnitude := {}, scaled := {}, load := {}
  , finiteElephant := {}, bullshit := {}, propaganda := {}, acolyte := {}
  , scientific := {}, truth := {}, witnessed := {}, real := {}, localGate := {}
  , universal := {}, logical := {}, halted := {}, measured := {}, compiled := {}
  , inferred := {} }

end Gates

end Measurement.Agent
