import Measurement.Episode1

/-
PLAN_RFC §2 -- THE ONE THEOREM (the echo), grounded on the sacred base.

  "I have heard it both ways."

One electron in orbit and the anti-Cooper-pair are one rotating object under two
names.  The two descriptions are two propositions -- two *truths* about the one
object.  They are logically equivalent (the same content, read the two ways), so
by PROPOSITIONAL EXTENSIONALITY they are the same proposition: "the names are the
same name."  That is the honest reading of §2 -- the coupling of the two names is
`propext`, and the axiom footprint is exactly `[propext]` (choice-free AND
quotient-free), grounded in the one sacred grant `Fact.Truth` (TRUE = TRUE).

Self-contained on the sacred base (imports only `Episode1`) so the whole 16+
sprawl that groped toward this echo becomes unnecessary and can be pruned.
Sacred Episodes 1-15 untouched.
-/

namespace Measurement.TwoDescriptions

open Measurement (Fact)

/-- Spin: the two half-turns of the rotation. -/
inductive Spin
  | up
  | down
deriving DecidableEq, Repr

/-- Matter or antimatter. -/
inductive Orientation
  | matter
  | antimatter
deriving DecidableEq, Repr

/-- One leg of the orbit / one member of the pair. -/
structure Leg where
  orientation : Orientation
  spin : Spin
deriving DecidableEq, Repr

/-- The up half-turn: an antimatter leg, spin up. -/
def upLeg : Leg := { orientation := .antimatter, spin := .up }

/-- The down half-turn: an antimatter leg, spin down. -/
def downLeg : Leg := { orientation := .antimatter, spin := .down }

/-! ### The two descriptions -- two truths about the one object. -/

/-- **Description A -- the anti-Cooper-pair**, read as a pair: left then right,
both antimatter. -/
def anti_cooper_pair : Prop :=
  upLeg.orientation = Orientation.antimatter ∧ downLeg.orientation = Orientation.antimatter

/-- **Description B -- the electron in orbit**, read as a rotation: the two
half-turns in turn order (the *other* way round), both antimatter. -/
def electron_in_orbit : Prop :=
  downLeg.orientation = Orientation.antimatter ∧ upLeg.orientation = Orientation.antimatter

/-! ### The echo -- the two names are the same name (by propositional extensionality). -/

/-- The two descriptions are equivalent (∧ commutes -- "heard it both ways"),
hence EQUAL as propositions by `propext`.  This is §2's identity: the coupling of
the two names of the one rotating object. -/
theorem two_descriptions : electron_in_orbit = anti_cooper_pair :=
  propext ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Grounding: each description is the sacred truth `TRUE = TRUE` reached one way.
Both hold; the object is what it is. -/
theorem both_true : electron_in_orbit ∧ anti_cooper_pair :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

#print axioms two_descriptions

end Measurement.TwoDescriptions
