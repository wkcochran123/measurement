/-
The argument, restated.

This file stands beside the device and is built apart: `lake build Experiments.Restated`.  Nothing in `Measurement`
imports it.  It defines no inductive.

The author's, 19 November 2026: starting at the physics of an equivalation, on the same difference, of a jar that
bangs the fact that the tree on the truth and the tree on the same are different: that restates the logical argument,
and the number comes out of it in very short order (declared).  The author wrote it with names the device does not
all have.  Here it is on the device's own constructors.  Two things in it are choices made in the writing and not the
author's: a jar that bangs must stand on a jar, and this one stands on the truth's label over the tree on the same;
and the reader that takes the number out is written here.
-/
import Measurement.Episode13

namespace Measurement
open readers_experience the_area
open «springer-verlag» THE_GOSPEL the_representation assembly_instructions

--| THE FACT THAT THEY ARE DIFFERENT.  A tree on the truth and a tree on the same.  What it says: they are two.  Asked only
--| whether it is true: they are one, for two facts that are true are one fact.  So this fact is said, and it does not click.
noncomputable def the_truth_and_the_same_are_different : FACT :=
  { truth := Area.tree FACT.Truth ≠ Area.tree the_same_inferred_from_the_experience
    click := .isFalse fun different =>
      different (congrArg Area.tree (two_facts_that_are_true_are_one_fact _ _ rfl and_it_is_so)) }

theorem it_is_said_and_it_does_not_hold : ¬ the_truth_and_the_same_are_different.truth :=
  fun different => different (congrArg Area.tree (two_facts_that_are_true_are_one_fact _ _ rfl and_it_is_so))

--| THE JAR, AND THE PHYSICS.
noncomputable def the_argument_in_a_jar : Jar :=
  .bang the_truth_and_the_same_are_different (.color FACT.Truth (.tree the_same_inferred_from_the_experience))
noncomputable def the_argument_restated : Equivalation := .physics SAME_DIFFERENCE the_argument_in_a_jar

--| Read by the device's own readers: the physics vanishes to the same difference, and the jar holds the tree on the same,
--| which is the tree on the truth.
theorem the_argument_vanishes_to_the_same_difference : the_argument_restated.vanish = [SAME_DIFFERENCE] := rfl

theorem the_jar_holds_the_same_and_it_is_the_truth :
    what_the_jar_holds the_argument_in_a_jar = .tree the_same_inferred_from_the_experience
      ∧ what_the_jar_holds the_argument_in_a_jar = .tree FACT.Truth :=
  ⟨rfl, congrArg Area.tree (two_facts_that_are_true_are_one_fact _ _ and_it_is_so rfl)⟩

--| THE NUMBER, IN SHORT ORDER.  What the same says is that nothing and the bent card are one.  So the argument holds one
--| count, the bent card, and the device has one more, the frame every arm carries.  From those two and nothing else:
--| the arm that clicks is the two together; the number is that arm cubed and the whole root, over the frame by the bent
--| card.  No crank is turned.
def the_bent_card_counted : Nat := cells the_gap_of_the_experience
def the_frame_counted : Nat := cells the_frame
def the_arm_that_clicks_counted : Nat := the_bent_card_counted + the_frame_counted

theorem thirteen_five_and_eighteen :
    the_bent_card_counted = 13 ∧ the_frame_counted = 5 ∧ the_arm_that_clicks_counted = 18
      ∧ cells the_gap_of_the_interpretation = 0 := by decide

--| The whole part: the arm cubed and the whole root of the arm to the fourth by the round trip, over the frame by the bent
--| card.  One hundred and thirty-seven, with nothing over.
theorem the_whole_part_in_one_line :
    3073 * 3073 ≤ the_arm_that_clicks_counted ^ 4 * (the_arm_that_clicks_counted * the_frame_counted)
      ∧ the_arm_that_clicks_counted ^ 4 * (the_arm_that_clicks_counted * the_frame_counted) < 3074 * 3074
      ∧ (the_arm_that_clicks_counted ^ 3 + 3073) / (the_frame_counted * the_bent_card_counted) = 137
      ∧ (the_arm_that_clicks_counted ^ 3 + 3073) % (the_frame_counted * the_bent_card_counted) = 0 := by decide

--| And all of it, at the device's scale.  The whole root, written out; that it is the whole root; and the number Episode 8
--| printed after a hundred and six turns of its crank, to the last place.
def the_whole_root_at_the_scale : Nat := 3073733885683664710702924525

set_option maxRecDepth 100000 in
theorem it_is_the_whole_root :
    the_whole_root_at_the_scale * the_whole_root_at_the_scale
        ≤ the_arm_that_clicks_counted ^ 4 * (the_arm_that_clicks_counted * the_frame_counted) * (10 ^ 24 * 10 ^ 24)
      ∧ the_arm_that_clicks_counted ^ 4 * (the_arm_that_clicks_counted * the_frame_counted) * (10 ^ 24 * 10 ^ 24)
        < (the_whole_root_at_the_scale + 1) * (the_whole_root_at_the_scale + 1) := by decide

set_option maxRecDepth 100000 in
theorem the_number_in_one_line :
    (the_arm_that_clicks_counted ^ 3 * 10 ^ 24 + the_whole_root_at_the_scale)
        / (the_frame_counted * the_bent_card_counted)
      = the_constant_factor_of_scaling_bullshit := by decide

end Measurement
