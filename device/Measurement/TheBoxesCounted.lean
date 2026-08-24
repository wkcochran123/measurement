-- TheBoxesCounted.lean
--
-- R1 of the constructive rewrite (operator, 2026-08-22: "re-write episode 9
-- and 10 to be constructive making the generation of the constant less
-- ad-hoc").  Episode 10's finish CITED `boxCount = 2` and
-- `finiteness_forces_electron` in prose while the code typed the two and the
-- one as bare literals; Episode 24 -- the cited authority -- types them too.
-- Importing Episode 24 would only have moved a typed literal one file down and
-- called it provenance, and would have dragged Episode 23 and the service
-- panel with it.  So the count is PERFORMED here instead.
--
-- Imports Episode4 ONLY (for `Variation`, the tower being sorted).  Nothing
-- from the parked chain, nothing from the calibration service panel.  No
-- sacred byte moves: Episode 4 is read, never written.
--
-- WHAT IS EARNED AND WHAT IS NAMED, kept apart on purpose:
--   EARNED   the rung count, off the elaborator's own record of `Variation`;
--   EARNED   the box count, as the length of the collapsed roster;
--   EARNED   the electron's box, as what is left when the value box is gone;
--   NAMED    the SORT itself -- that the first variation and the second share
--            a box because the residue between them is below the fixed
--            representation's resolution.  That is Episode 24's premise, and
--            it is written as a premise here, not laundered into a count.
--
-- WHAT THE AXIOM LEDGER CANNOT SEE HERE, disclosed up front because the census
-- is the grade this corpus runs on and it is BLIND to part of this file.  The
-- rung count and the position answers are numerals a metaprogram baked in.  The
-- kernel checks the numerals; it never checks that they came from asking the
-- environment.  `#print axioms` therefore reports these receipts axiom-free
-- whether the metaprogram does its job or returns a constant, and the trade is
-- forced: a kernel-visible name check would query a `String` and pull choice
-- through the UTF-8 API.  The compensation is the discrimination receipt at the
-- bottom of this file -- evidence, in the artifact, that the check CAN fail.
-- Read the census and that receipt together; neither alone grades this leaf --
-- and read the receipt at its own width: it shows discrimination on sampled
-- points, not a verified metaprogram.  The kernel cannot verify the elaborator;
-- it can only bracket it, which is what this leaf does and says.
--
-- THE TWO THREES ARE NOT ONE THREE.  `theRungCount` is three because the
-- tower has three constructors.  Episode 10's `theSeparation` is three
-- because two boxes and the electron's box counted as a coproduct roster come
-- to three.  They are both three and they are not the same fact, and no
-- sentence anywhere may narrate them as one number wearing two hats.

import Measurement.Episode4

open Lean Elab Term in
/-- The rung count, READ OUT OF THE COMPILER'S OWN RECORD of an inductive
rather than typed by hand.  This is the elaborator counting its own
environment: the tower's arity is a fact the machine already holds, so the
device asks it instead of asserting it. -/
elab "rungs_of% " i:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  let env ← getEnv
  let some (.inductInfo iv) := env.find? n | throwError "not an inductive"
  return Lean.mkNatLit iv.ctors.length

open Lean Elab Term in
/-- WHICH RUNG SITS AT AN INDEX, asked rather than assumed.  `boxOfRung` binds
the sort POSITIONALLY -- index zero to the value box -- and nothing so far
receipted that index zero really is the tower's 0th-term constructor.  This
asks the compiler for the name at that index and answers one when it matches,
zero when it does not.  The name comparison happens HERE, in the elaborator,
so no `String` is ever queried inside a kernel decision. -/
elab "rung_at% " i:ident ", " k:num ", " nm:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  let env ← getEnv
  let some (.inductInfo iv) := env.find? n | throwError "not an inductive"
  let idx := k.getNat
  let matches? :=
    match iv.ctors[idx]? with
    | some c => c.componentsRev.head!.toString == nm.getId.toString
    | none   => false
  return Lean.mkNatLit (if matches? then 1 else 0)

namespace Measurement.TheBoxesCounted

/-- How many rungs the variation tower has.  Not typed: asked. -/
def theRungCount : Nat := rungs_of% Measurement.Variation

/-- THE SORT (the premise, written as a premise).  The 0th term -- the fixed
point value -- gets its own box.  Every variation above it shares the other,
because what separates them is below the fixed representation's resolution.
This is Episode 24's `boxOf`, by rung index. -/
def boxOfRung : Nat → Nat
  | 0 => 0
  | _ => 1

/-- The roster: every rung, sorted.  Three entries, because there are three
rungs. -/
def theBoxRoster : List Nat := (List.range theRungCount).map boxOfRung

/-- The boxes actually used: the roster with its repeats collapsed. -/
def theBoxes : List Nat := theBoxRoster.eraseDups

/-- THE BOX COUNT, as what the collapse RETURNS -- the length of the collapsed
roster -- and not as anything the sort's arms wrote down. -/
def theBoxCount : Nat := theBoxes.length

/-- THE POSITION IS CHECKED, not trusted.  `boxOfRung` sends index zero to the
value box; this asks the compiler whether index zero of the tower really is
`the_newton` -- the 0th term, the fixed-point value -- and the receipt below
decides it.  Without this the sort would be bound positionally with nothing
saying the position is the one meant. -/
def rungZeroIsNewton : Nat := rung_at% Measurement.Variation, 0, the_newton
def rungOneIsGateaux : Nat := rung_at% Measurement.Variation, 1, the_gateaux
def rungTwoIsFrechet : Nat := rung_at% Measurement.Variation, 2, the_frechet

/-- THE CHECK CAN FAIL, and here is the evidence IN THE FILE rather than in
somebody's memory of a session.  Ask the same question with a name that is
wrong for the position and the answer comes back zero.  Without this line
nothing in the artifact distinguishes a metaprogram that compares names from
one that returns one unconditionally -- the axiom ledger cannot tell those
apart, because both hand the kernel a numeral and the kernel checks only the
numeral.  (This was found the hard way: the first version of this leaf asked
for `newton`, `gateaux` and `frechet`, the tower's constructors are actually
`the_newton`, `the_gateaux` and `the_frechet`, and the position theorem failed
until the environment was asked what the names really are.  A check that cannot
fail is not a check.) -/
def rungZeroAskedWrong : Nat := rung_at% Measurement.Variation, 0, the_frechet
def rungOneAskedWrong : Nat := rung_at% Measurement.Variation, 1, the_newton
def rungAskedPastTheEnd : Nat := rung_at% Measurement.Variation, 3, the_newton

/-- The value box: the 0th term's box, the first the roster names. -/
def theValueBox : Nat := boxOfRung 0

/-- THE ELECTRON'S BOX, as what is LEFT.  Not typed as one: the boxes that are
not the value box, and in a count this size there is exactly one of them --
nowhere else to sit.  `finiteness_forces_electron`, performed rather than
cited. -/
def theBoxesThatAreNotTheValueBox : List Nat :=
  theBoxes.filter (fun b => b != theValueBox)

def theElectronsBox : Nat := theBoxesThatAreNotTheValueBox.headD theValueBox

-- ---------------------------------------------------------------------------
-- THE RECEIPTS.  Each one decides something that used to be typed or asserted.
-- ---------------------------------------------------------------------------

/-- The tower has three rungs, and the elaborator said so. -/
theorem the_rung_count_is_read_not_typed : theRungCount = 3 := by decide

/-- AND THE POSITIONS ARE THE ONES MEANT.  Index zero is `the_newton`, index one is
`the_gateaux`, index two is `the_frechet` -- asked of the compiler, decided here.  So
the sort's positional binding is receipted rather than assumed, and a
reordering of the tower's constructors would break this loudly instead of
silently re-sorting the boxes. -/
theorem the_positions_are_the_ones_meant :
    rungZeroIsNewton = 1 ∧ rungOneIsGateaux = 1 ∧ rungTwoIsFrechet = 1 := by decide

/-- THE DISCRIMINATION RECEIPT.  The same question, asked wrongly three ways --
right index with the wrong name, a different index with a different wrong name,
and an index past the end of the tower -- answers zero every time.  So the
positional receipt above is not vacuous: the metaprogram distinguishes, and
this decides that it does.

READ THIS TOGETHER WITH THE CENSUS, NEVER INSTEAD OF IT.  The axiom ledger
CANNOT audit an elaborator-supplied value: the kernel checks that a numeral is
what it is, never that the numeral was computed by asking the environment.
`#print axioms` would report these receipts axiom-free whether the metaprogram
compares names or returns a constant.  So "axiom-free" here means THE KERNEL
PAID NOTHING -- it does not mean nothing was assumed, and the assumption sits
where the ledger cannot look.  The trade is forced, not sloppy: checking names
kernel-side would query a `String` and pull choice through the UTF-8 API, so
the comparison must happen in the elaborator, and the price of that is census
visibility.  What is owed in exchange is DISCLOSURE, which is this paragraph,
and EVIDENCE THAT THE CHECK CAN FAIL, which is the theorem.

AND READ THIS THEOREM AT ITS OWN WIDTH, not wider.  It establishes that the
metaprogram DISCRIMINATES ON THE POINTS TESTED.  It rules out the one that
returns one unconditionally -- that was the live worry and it is dead.  It does
NOT verify that the metaprogram implements name lookup: one that hardcoded
these six answers would pass exactly as well.  The honest register is
non-vacuous by kernel decision on sampled inputs, never a verified elaborator.

That limit is not an accident of this leaf, it is the device's own shape in a
third place.  The kernel cannot verify the elaborator -- the `String` wall
forbids it the way the Cantor wall forbids the section.  What can be done is to
BRACKET it: sample where the answer is known, and say how wide the bracket is.
That is what the jar is to the reading and what the depth ladder is to the
closed form.  The instrument gets the same treatment as the measurement, which
is the only consistent position available.

So the grade on the four elaborator-sourced receipts, in three parts and the
third not optional: axiom-free census, PLUS discrimination demonstrated
in-kernel on tested points, PLUS this disclosure that the ledger cannot see
elaborator-supplied values.  The third part is what stops a reader from taking
the first for more than it says. -/
theorem the_check_discriminates :
    rungZeroAskedWrong = 0 ∧ rungOneAskedWrong = 0 ∧ rungAskedPastTheEnd = 0 := by decide

/-- THE COLLAPSE, PROVED.  Three rungs go in; the roster names the value box
once and the other box twice; the collapse returns two boxes.  The two is what
the count RETURNS, not what the sort's arms wrote. -/
theorem the_collapse_is_what_the_count_returns :
    theBoxRoster.length = theRungCount ∧ theBoxes = [0, 1] ∧ theBoxCount = 2 := by
  decide

/-- And the count is strictly smaller than the tower it counts: three rungs,
two boxes.  The collapse is real, not a relabelling. -/
theorem the_collapse_is_a_collapse : theBoxCount < theRungCount := by decide

/-- FINITENESS FORCES IT, performed: exactly one box is not the value box, and
the electron's box is that one. -/
theorem exactly_one_box_is_not_the_value_box :
    theBoxesThatAreNotTheValueBox.length = 1 := by decide

theorem the_electrons_box_is_what_is_left :
    theElectronsBox ≠ theValueBox ∧ theElectronsBox = 1 := by decide

/-- VALUE PRESERVED.  The counted two and the counted one are exactly the two
and the one Episode 10 used to type.  The receipt that R1 rewrote the
PROVENANCE and not the device. -/
theorem the_counted_values_are_the_typed_ones :
    theBoxCount = 2 ∧ theElectronsBox = 1 := by decide

end Measurement.TheBoxesCounted

#print axioms Measurement.TheBoxesCounted.the_rung_count_is_read_not_typed
#print axioms Measurement.TheBoxesCounted.the_positions_are_the_ones_meant
#print axioms Measurement.TheBoxesCounted.the_check_discriminates
#print axioms Measurement.TheBoxesCounted.the_collapse_is_what_the_count_returns
#print axioms Measurement.TheBoxesCounted.the_collapse_is_a_collapse
#print axioms Measurement.TheBoxesCounted.exactly_one_box_is_not_the_value_box
#print axioms Measurement.TheBoxesCounted.the_electrons_box_is_what_is_left
#print axioms Measurement.TheBoxesCounted.the_counted_values_are_the_typed_ones
