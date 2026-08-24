-- TheCensusComparison.lean
--
-- THE DATA for the operator's hypothesis (2026-08-22): "the difference between
-- the elaboration measurement and the elaboration derivation can be placed in
-- the hidden memory of the compiler."
--
-- The gate-form both chairs settled on: run BOTH paths, and compare.  If the
-- twin and the story rung report the SAME value while their censuses DIFFER,
-- the difference is located in what the compiler remembered.  If the values
-- differ, it fails in the open and no bookkeeping saves it.
--
-- This file RUNS that comparison and prints it into the build log.  It draws
-- no conclusion: the reading below is evidence for the gate, not a verdict,
-- and the seat that built the tie does not get to grade it.
--
-- READ THE TIE'S SCOPE EXACTLY, because an earlier version of this header
-- overclaimed it and the overclaim was load-bearing.  `TheTwinTiedToTheTrips`
-- proves that a reader using `gawk_at._default` advances the head exactly as
-- the twin says, at every trip count.  It does NOT mention `POW`, `POWER` or
-- `POWEST` by name, and it cannot: that leaf imports Episode 4 and the twin,
-- not Episode 9.  So what is printed below is the census of six NAMED rungs
-- beside the census of a twin tied to the DEFAULT those rungs use -- not to
-- those rungs by name.  Connecting the named rungs is a further theorem, in
-- Episode 9's own context, and it is OWED rather than assumed here.
--
-- Consequently this file does not establish the "same value" half of the
-- hypothesis's antecedent for the named rungs.  It prints two censuses; what
-- may be inferred from them is the gate's business, and the honest reading on
-- the record is NOT ESTABLISHED -- which is not the same word as failed.

import Measurement.Episode9
import Measurement.SupportingMeasurements.TheReadPathTwin
import Measurement.SupportingMeasurements.TheTwinTiedToTheTrips

/-%Y% /* the derivation side: the story's own rungs, named and elaborated */ %Y%-/
#print axioms Measurement.POW
#print axioms Measurement.POWER
#print axioms Measurement.POWEST
#print axioms Measurement.AN_EXAMPLE_OF_YOURSELF
#print axioms Measurement.theKnowersNeedle
#print axioms Measurement.the_superpigeon

/-%Y% /* the measurement side: the same heads, computed */ %Y%-/
#print axioms Measurement.TheReadPathTwin.headAfter
#print axioms Measurement.TheReadPathTwin.trip_zero_reads_the_pin
#print axioms Measurement.TheReadPathTwin.trip_one_reads_the_threshold
#print axioms Measurement.TheReadPathTwin.trip_two_reads_the_response
#print axioms Measurement.TheReadPathTwin.the_ladder_saturates_at_three

/-%Y% /* the tie: why the two are comparable at all */ %Y%-/
#print axioms Measurement.TheTwinTiedToTheTrips.the_default_gawk_steps_the_head
#print axioms Measurement.TheTwinTiedToTheTrips.the_trips_climb_the_twins_ladder

/-%Y% /* and the value, from the side that can actually be run */ %Y%-/
#eval ("the heads, run", Measurement.TheReadPathTwin.theTripLadder)
