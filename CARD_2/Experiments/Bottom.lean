/-
The bottom of the last machine, and the table beside it.

This file stands beside the device and is built apart: `lake build Experiments.Bottom`.  Nothing in `Measurement`
imports it.  It defines no inductive.

Episode 13 wrote the device's processes out from the bottom.  Here what the lowest of them carry is read all the way
down and counted, in facts.  The author's, 21 November 2026 (declared): the quarter at the bottom is the opposite of
the daisy, and it clicks; the Cauchy process's nine and nine are eighteen, and the thing that does not click does not
get the other side of the bracket; and the table is to be set beside these, the lengths all being the same
computation.  Asked whether that was an assumption, the author: "not my assumption, only one build process."  That is
so: there is one build, and in it the kernel computes both sides of every statement below and finds them one, by
`rfl`.  Episode 8 takes its eighteen and its five from the lengths of tapes in its list of steps; these come from the
processes.  What `rfl` does not show is narrower: that either count was derived from the other.

The author has looked at the code and interprets these values as the application of the matrix described in
Episode 8 (declared).
-/
import Measurement.Episode13

namespace Measurement

section the_bottom_of_the_last_machine
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| WHAT THE LOWEST PROCESSES CARRY, IN FACTS.  Read all the way down.  The carrier's quarter, two.  The count, three.  The
--| origin, five.  The limit, five, and its sequence, seven.  The Cauchy process's value, nine, and its accumulation, nine.
--| The observation's before, nine, and its after, thirty.
theorem what_the_lowest_processes_carry :
    the_carrier_process.quarter.all_the_way_down.length = 2
      ∧ the_counting_process.count.all_the_way_down.length = 3
      ∧ the_indexing_process.origin.all_the_way_down.length = 5
      ∧ the_limit_process.limit.all_the_way_down.length = 5
      ∧ the_limit_process.sequence.all_the_way_down.length = 7
      ∧ the_cauchy_process.value.all_the_way_down.length = 9
      ∧ the_cauchy_process.accumulation.all_the_way_down.length = 9
      ∧ the_observation_process.before.all_the_way_down.length = 9
      ∧ the_observation_process.after.all_the_way_down.length = 30 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

--| The lowest count is three facts.  By Episode 8's own reader of a count, which does not look inside the quarter, it is two.
--| It is not thirteen.
theorem the_lowest_count_is_three_and_by_its_own_reader_two :
    the_counting_process.count = Natural.number FACT.Truth (Number.zero FACT.Truth) (Natural.zero FACT.Truth)
      ∧ the_counting_process.count.all_the_way_down.length = 3
      ∧ the_counting_process.count.induct.length = 2 := ⟨rfl, rfl, rfl⟩

--| THE QUARTER AT THE BOTTOM CLICKS.  A one on a zero, both on the truth, and both click.  Nothing is handed in and nothing
--| is chosen.
theorem the_quarter_at_the_bottom_is_the_truth_twice_and_it_clicks :
    the_carrier_process.symbol = FACT.Truth
      ∧ the_carrier_process.quarter = Number.one FACT.Truth (Number.zero FACT.Truth)
      ∧ the_carrier_process.quarter.all_the_way_down.map the_representation.the_click = [true, true] := by
  refine ⟨rfl, rfl, ?_⟩; decide

--| THE BRACKET AND THE LIMIT.  The Cauchy process holds two things, a value and an accumulation: a bracket with both its
--| sides.  The limit process under it holds one limit.
noncomputable def the_bracket_at_the_bottom : Nat :=
  the_cauchy_process.value.all_the_way_down.length + the_cauchy_process.accumulation.all_the_way_down.length
noncomputable def the_limit_at_the_bottom : Nat := the_limit_process.limit.all_the_way_down.length

theorem the_bracket_is_eighteen_and_the_limit_is_five :
    the_bracket_at_the_bottom = 18 ∧ the_limit_at_the_bottom = 5
      ∧ the_bracket_at_the_bottom - the_limit_at_the_bottom = 13 := ⟨rfl, rfl, rfl⟩

--| Every fact in the bracket and in the limit clicks: twenty-three of them.
theorem every_fact_in_the_bracket_and_the_limit_clicks :
    (the_cauchy_process.value.all_the_way_down ++ the_cauchy_process.accumulation.all_the_way_down
        ++ the_limit_process.limit.all_the_way_down).map the_representation.the_click
      = List.replicate 23 true := by decide

end the_bottom_of_the_last_machine

section the_table_beside_it
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions readers_experience the_table
attribute [local instance high] rung01 rung02 rung03 rung04 rung05 rung06 rung07 rung08 rung09 rung10 rung11 rung12 rung13 rung14 rung15
  rung16 rung17 rung18 rung19 rung20 rung21 rung22 rung23 rung24 rung25 rung26 rung27 rung28 rung29 rung32 rung33 rung34 rung35 a_truth_about_the_experience

--| EPISODE 8'S THREE NUMBERS, AND THESE.  The arm that clicks is the bracket.  The frame on every arm is the limit.  The bent
--| card is the one less the other.  Each by rfl: one number, reached two ways.
theorem episode_eights_three_numbers_are_the_bracket_the_limit_and_the_one_less_the_other :
    readers_experience.the_macguffin = the_bracket_at_the_bottom
      ∧ the_dimensions_of_universe = the_limit_at_the_bottom
      ∧ readers_experience.bent_card = the_bracket_at_the_bottom - the_limit_at_the_bottom := ⟨rfl, rfl, rfl⟩

--| THE FOUR ARMS.  True on true, false on true and false on false each store a fact that can click, and each weighs the
--| bracket: both sides.  True on false stores a fact that cannot, and weighs the limit: one side, and no other.
theorem the_three_arms_that_click_weigh_the_bracket_and_the_one_that_does_not_weighs_the_limit :
    the_arm_weight true true = the_bracket_at_the_bottom
      ∧ the_arm_weight false true = the_bracket_at_the_bottom
      ∧ the_arm_weight false false = the_bracket_at_the_bottom
      ∧ the_arm_weight true false = the_limit_at_the_bottom := ⟨rfl, rfl, rfl, rfl⟩

theorem an_arm_weighs_the_bracket_where_it_can_click_and_the_limit_where_it_cannot (this that : Bool) :
    the_arm_weight this that
      = if the_arm_stores_a_fact_that_can_click this that then the_bracket_at_the_bottom else the_limit_at_the_bottom := by
  cases this <;> cases that <;> rfl

--| THE TABLE.  Episode 12's table of the four arms is the bracket and the limit over the bracket and the bracket.
theorem the_table_is_the_bracket_and_the_limit :
    the_derived_click_table
      = ((the_bracket_at_the_bottom, the_limit_at_the_bottom), (the_bracket_at_the_bottom, the_bracket_at_the_bottom)) := rfl

--| And the residual's three numbers: the bent card, twice the bracket, and the bracket.
theorem the_residuals_numbers_are_the_one_less_the_other_twice_the_bracket_and_the_bracket :
    the_bracket_at_the_bottom - the_limit_at_the_bottom = 13
      ∧ 2 * the_bracket_at_the_bottom = 36
      ∧ the_bracket_at_the_bottom = 18 := ⟨rfl, rfl, rfl⟩

end the_table_beside_it

--#print axioms what_the_lowest_processes_carry
--#print axioms every_fact_in_the_bracket_and_the_limit_clicks
--#print axioms the_three_arms_that_click_weigh_the_bracket_and_the_one_that_does_not_weighs_the_limit
--#print axioms the_table_is_the_bracket_and_the_limit

end Measurement
