/-
PLAN §2 -- THE ONE THEOREM (the echo).

  "I have heard it both ways."

One electron in orbit and the anti-Cooper-pair are one rotating object under two
names.  The equality is DEFINITIONAL: the two descriptions are built by different
routes and reduce to the same term (`:= rfl`).  This is `1 = 0.999...` generalized
-- the thing has more than one name and the names are the same name.

Self-contained on purpose: it declares its own minimal substrate so the whole
16+ sprawl that groped toward this echo becomes unnecessary (PLAN §4/§5.3) and can
be removed without taking the echo down with it.  Sacred Episodes 1-15 untouched.
-/

namespace Measurement.TwoDescriptions

/-- Spin: the two half-turns of the rotation. -/
inductive Spin
  | up
  | down
deriving DecidableEq, Repr

/-- Matter or antimatter: the two charge orientations. -/
inductive MatterOrientation
  | matter
  | antimatter
deriving DecidableEq, Repr

/-- One member of the pair / one leg of the orbit. -/
structure PairMember where
  orientation : MatterOrientation
  spin : Spin
deriving DecidableEq, Repr

/-- Two legs read together: a Cooper-pair channel / a full turn of the orbit. -/
structure Channel where
  left : PairMember
  right : PairMember
deriving DecidableEq, Repr

/-! ### Description A -- the anti-Cooper-pair (read as a pair)

Two antimatter members, spins balanced up/down. -/
def anti_cooper_pair : Channel :=
  { left  := { orientation := .antimatter, spin := .up }
    right := { orientation := .antimatter, spin := .down } }

/-! ### Description B -- the electron in orbit (read as a rotation)

Start from ONE electron -- matter, spin up.  Put it in orbit: a rotation with two
half-turns.  Going *around* the loop is the positron reading (§3): the return leg
is charge-conjugated (matter -> antimatter).  The first half-turn is the up leg,
the second is the down leg. -/
def electron : PairMember :=
  { orientation := .matter, spin := .up }

/-- Around the loop: charge-conjugate (the positron reading of the return leg). -/
def conjugateReturn (m : PairMember) : PairMember :=
  { m with orientation := .antimatter }

/-- The second half-turn: the other half of the rotation. -/
def halfTurnDown (m : PairMember) : PairMember :=
  { m with spin := .down }

def electron_in_orbit : Channel :=
  { left  := conjugateReturn electron
    right := conjugateReturn (halfTurnDown electron) }

/-! ### The echo -- the two descriptions are the same by `rfl`. -/
theorem two_descriptions : electron_in_orbit = anti_cooper_pair := rfl

#print axioms two_descriptions

end Measurement.TwoDescriptions
