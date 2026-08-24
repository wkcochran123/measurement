-- TheOutputIsOneValue.lean
--
-- CLAUSE 2 of the finished-definition: the operator's one requirement, that
-- the output be unambiguous or the variable name must change.  The roster
-- carries a name, `unambiguous_output`; this leaf is where that name is
-- earned or lost.
--
-- WHY THIS IS A SEPARATE FILE, and it is not a filing convenience.  Episode 10
-- is BLIND on purpose: "no target is written in this file, no expected value,
-- no bracket... Numbers read last."  A pinned-literal receipt writes the
-- expected value into the source, so putting these theorems in Episode 10
-- would satisfy clause 2 by destroying the blindness the reading depends on.
-- The pin therefore lives DOWNSTREAM of the blind read: Episode 10 computes
-- without knowing what it will get, and this file, importing the result,
-- records what it got.  The order matters -- blind first, pinned after.
--
-- WHAT "UNAMBIGUOUS" MEANS HERE, and what it does not.  It means the output is
-- ONE DETERMINATE VALUE: determinism by construction, because these are
-- functions and not relations, plus a decided literal equality per output, so
-- "the output IS this value" is checked rather than described.  It does NOT
-- mean the value is identical to any other recorded number.  A number can be
-- perfectly unambiguous as itself and still stand in same_difference to
-- another; those are different axes, and nothing here claims the second.
--
-- No string is QUERIED anywhere below -- the pins are on whole numbers and
-- ratios.  Querying a `String` would pull choice through the UTF-8 API and
-- turn an axiom-free receipt into a purchased one.

import Measurement.Episode10

namespace Measurement.TheOutputIsOneValue

/-- THE CARDS ARE ONE VALUE. -/
theorem the_cards_are_one_value : cardC = 18 ∧ cardT = 5 ∧ cardR = 18 := by decide

/-- THE CROSSING IS ONE VALUE, at the depth the story reads at. -/
theorem the_crossing_is_one_value : dStarScaled = 1897366596 := by decide

/-- THE RECIPROCAL IS ONE VALUE, as an exact ratio of whole numbers -- pinned
where it is a ratio, before any decimal is spelled, so nothing here depends on
how the digits are printed. -/
theorem the_reciprocal_is_one_value :
    invAlphaJar = ((614746777104 : Int), (4486832980 : Int)) := by decide

/-- And the counted inputs are one value too, so the pin covers the whole chain
from the boxes to the ratio and not merely its last step. -/
theorem the_counted_inputs_are_one_value :
    theTwoBoxes = 2 ∧ theElectronsBox = 1 ∧ theSeparation = 3 ∧ theCoupling = 18 := by
  decide

/-- THE ACCEPTANCE BIT.  Every output above is pinned to one value, decided,
with no choice and no string query.  On this rung the name
`unambiguous_output` is earned. -/
theorem the_name_is_earned :
    (cardC = 18 ∧ cardT = 5 ∧ cardR = 18)
    ∧ dStarScaled = 1897366596
    ∧ invAlphaJar = ((614746777104 : Int), (4486832980 : Int)) := by
  decide

end Measurement.TheOutputIsOneValue

#print axioms Measurement.TheOutputIsOneValue.the_cards_are_one_value
#print axioms Measurement.TheOutputIsOneValue.the_crossing_is_one_value
#print axioms Measurement.TheOutputIsOneValue.the_reciprocal_is_one_value
#print axioms Measurement.TheOutputIsOneValue.the_counted_inputs_are_one_value
#print axioms Measurement.TheOutputIsOneValue.the_name_is_earned
