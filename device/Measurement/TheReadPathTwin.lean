-- TheReadPathTwin.lean
--
-- R6 of the constructive rewrite: the COMPUTABLE TWIN of Episode 9's read
-- path.  Episode 9's trips (POW, POWER, POWEST) are `noncomputable`, so the
-- read path can be named but not RUN.  This leaf carries the same head
-- selection as a total, computable function that `#eval` can execute, and
-- proves the algebra the story's reader performs.
--
-- STORY UNTOUCHED.  Nothing here edits Episode 9.  The twin is a leaf; the
-- tie between twin and story is a theorem, never an edit.
--
-- WHAT IS CLAIMED HERE, exactly: the head of a reading advances by one step
-- per gawk, and saturates.  The `.zero` reading gawks to a `.one` head; a
-- `.one` head gawks to `.rest_call`; a `.rest_call` head gawks to
-- `.rest_call` forever.  That is read off Episode 4's `gawk_at` (Ep4:1388),
-- where every branch of every arm -- all four `decTruth` cases in the `.one`
-- arm and all four in the `.rest_call` arm -- returns the same constructor.
-- The head does not depend on the truth values; only the payload does.
--
-- WHAT IS NOT CLAIMED HERE: that the story's readers use this step.  The
-- reader's `gawk_at` is a structure field with a DEFAULT, so a reader could
-- in principle supply another.  Tying the twin to the trips as the story
-- actually builds them is a separate theorem, in Episode 9's own context,
-- and it is owed -- it is not quietly assumed here.

import Measurement.Episode4

namespace Measurement.TheReadPathTwin

/-- The head of a reading: which constructor it is, and nothing else.  The
payload is not consulted, because the head selection does not consult it. -/
inductive Head where
  | zero
  | one
  | rest_call
deriving DecidableEq, Repr

/-- The head of an actual reading.  Total and computable. -/
def headOf : Bullshit → Head
  | .zero _                        => .zero
  | .one _ _ _ _ _                 => .one
  | .rest_call _ _ _ _ _ _ _ _ _ _ => .rest_call

/-- ONE GAWK, on heads alone.  This is Episode 4's `gawk_at` with the payload
forgotten: `.zero` becomes `.one`, and everything above `.zero` becomes
`.rest_call` and stays there. -/
def stepHead : Head → Head
  | .zero      => .one
  | .one       => .rest_call
  | .rest_call => .rest_call

/-- THE TRIP READ, COMPUTABLY.  The head after `n` gawks from the pin.  This
is the twin of the trip ladder: trip zero is the pin itself (no gawk), trip
one is one gawk, trip two is two.  Total -- no partial, no unsafe, no
`noncomputable`. -/
def headAfter : Nat → Head
  | 0     => .zero
  | n + 1 => stepHead (headAfter n)

/-- The whole ladder as the device runs it, so the read path has an output
that can actually be printed. -/
def theTripLadder : List Head := (List.range 3).map headAfter

#eval ("the read path, run", theTripLadder)
#eval ("the head at each trip", headAfter 0, headAfter 1, headAfter 2)

-- ---------------------------------------------------------------------------
-- THE RECEIPTS.
-- ---------------------------------------------------------------------------

/-- EXACTLY ONE HEAD PER TRIP, pinned to a literal.  Determinism is by
construction -- `headAfter` is a function, not a relation -- and the value is
pinned here so "the output IS this value" is decided, not described. -/
theorem trip_zero_reads_the_pin      : headAfter 0 = Head.zero      := by decide
theorem trip_one_reads_the_threshold : headAfter 1 = Head.one       := by decide
theorem trip_two_reads_the_response  : headAfter 2 = Head.rest_call := by decide

/-- The ladder, pinned as one value. -/
theorem the_trip_ladder_is_one_value :
    theTripLadder = [Head.zero, Head.one, Head.rest_call] := by decide

/-- THE COUNT TO THREE IS WHERE IT STOPS.  The third trip saturates: gawking a
`.rest_call` head returns a `.rest_call` head, so no fourth head exists to be
found.  "I counted your power to three" is a fixed point, and this decides
it. -/
theorem the_ladder_saturates_at_three (n : Nat) :
    headAfter (n + 2) = Head.rest_call := by
  induction n with
  | zero => decide
  | succ k ih =>
      show stepHead (headAfter (k + 2)) = Head.rest_call
      rw [ih]; rfl

/-- And the three heads are distinct -- the ladder climbs, it does not sit. -/
theorem the_three_heads_are_distinct :
    headAfter 0 ≠ headAfter 1 ∧ headAfter 1 ≠ headAfter 2 := by decide

/-- THE HEAD SELECTION IGNORES THE PAYLOAD, which is why a head-only twin is
faithful at all: any two readings with the same head have the same head after
a step. -/
theorem the_step_reads_only_the_head (b c : Bullshit) (h : headOf b = headOf c) :
    stepHead (headOf b) = stepHead (headOf c) := by rw [h]

end Measurement.TheReadPathTwin

#print axioms Measurement.TheReadPathTwin.trip_zero_reads_the_pin
#print axioms Measurement.TheReadPathTwin.trip_one_reads_the_threshold
#print axioms Measurement.TheReadPathTwin.trip_two_reads_the_response
#print axioms Measurement.TheReadPathTwin.the_trip_ladder_is_one_value
#print axioms Measurement.TheReadPathTwin.the_ladder_saturates_at_three
#print axioms Measurement.TheReadPathTwin.the_three_heads_are_distinct
#print axioms Measurement.TheReadPathTwin.the_step_reads_only_the_head
