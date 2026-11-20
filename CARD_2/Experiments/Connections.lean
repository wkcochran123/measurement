/-
The connections.

This file stands beside the device and is built apart: `lake build Experiments.Connections`.  Nothing in `Measurement`
imports it.  It defines no inductive.  Every line is the device's own: the sixteen steps, the four arms, the curvature
across, the contraction, the pairs of arms.

A reader of the device set four things side by side, 19 November 2026: the four arms; the sixteen steps, a compile arm
and an execute arm; the thirty-six comparisons of a pair of arms with a pair of arms; and the reviewer's thirty-six
pages.  The first three are joined here.  The fourth is not: no line of this file sends a page to a pair of pairs.
-/
import Measurement.Episode13

namespace Measurement
open readers_experience the_area

--| THE RESIDUE OF A STEP.  What execute counts, less what compile built.
def the_residue_of_a_step (step : (Bool × Bool) × (Bool × Bool)) : Int :=
  (cells (what_execute_counts step) : Int) - (cells (what_compile_builds step) : Int)

--| Ten are level.  Three are short by the bent card and three are over by it.
theorem ten_are_level_three_are_short_and_three_are_over :
    the_sixteen_steps.map the_residue_of_a_step
      = [0, -13, 0, 0,
         13,  0, 13, 13,
         0, -13, 0, 0,
         0, -13, 0, 0] := by decide

--| Asked what the two arms say: an arm says its coins are one coin, or says they are not.  Eight steps say the same thing
--| twice and eight do not.
def says_the_same_twice (step : (Bool × Bool) × (Bool × Bool)) : Bool :=
  (step.1.1 == step.1.2) == (step.2.1 == step.2.2)

theorem eight_say_the_same_twice_and_eight_do_not :
    (the_sixteen_steps.filter says_the_same_twice).length = 8
      ∧ (the_sixteen_steps.filter fun step => !says_the_same_twice step).length = 8 := by decide

--| Of the eight that do not, four have true on true on one side.  Their residues: two zeros, one up and one down.
theorem about_true_on_true_two_zeros_one_up_and_one_down :
    ((the_sixteen_steps.filter fun step =>
        !says_the_same_twice step && (step.1 == (true, true) || step.2 == (true, true))).map
      fun step => (step, the_residue_of_a_step step))
      = [(((true, true), (true, false)), -13),
         (((true, true), (false, true)), 0),
         (((true, false), (true, true)), 13),
         (((false, true), (true, true)), 0)] := by decide

--| And the other four have false on false on one side: the same again.
theorem about_false_on_false_two_zeros_one_up_and_one_down :
    ((the_sixteen_steps.filter fun step =>
        !says_the_same_twice step && (step.1 == (false, false) || step.2 == (false, false))).map
      the_residue_of_a_step)
      = [13, 0, -13, 0] := by decide

--| THE RESIDUES, A PAIR BY A PAIR.  The residue between two arms is a table on the arms: the second arm's weight less the
--| first's.  Its curvature across, for any weights at all, is one pair's residue by the other pair's.
theorem the_residues_across_are_one_pairs_residue_by_the_others (weight : Direction → Int) (a b c d : Direction) :
    the_curvature_across (fun this that => weight that - weight this) a b c d
      = (weight a - weight b) * (weight c - weight d) := by
  simp only [the_curvature_across, Int.sub_mul, Int.mul_sub]; ac_nf; omega

def the_residue_between (this that : Direction) : Int :=
  (the_arm_weight that.1 that.2 : Int) - (the_arm_weight this.1 this.2 : Int)
def the_residues_across (pairs : (Direction × Direction) × (Direction × Direction)) : Int :=
  the_curvature_across the_residue_between pairs.1.1 pairs.1.2 pairs.2.1 pairs.2.2

--| On the device's weights nine of the thirty-six are not nothing, and each is the bent card by the bent card.
theorem nine_of_the_thirty_six_are_the_bent_card_by_itself :
    (the_pairs_of_pairs.map the_residues_across).filter (· != 0)
      = [169, -169, -169, -169, 169, 169, -169, 169, 169] := by decide

--| They are the nine where both pairs hold the arm that does not click.
theorem they_are_the_nine_where_both_pairs_hold_the_arm_that_does_not_click :
    (the_pairs_of_pairs.filter fun pairs => the_residues_across pairs != 0)
      = (the_pairs_of_pairs.filter fun pairs =>
          (pairs.1.1 == (true, false) || pairs.1.2 == (true, false))
            && (pairs.2.1 == (true, false) || pairs.2.2 == (true, false))) := by decide

--| THE SOURCE'S THIRTY-SIX, CLOSED.  Close the six by six of the source back onto the four arms by the signs of three and
--| one.  It is eighteen of: twenty-three on every arm, and eight by the metric.
theorem the_sources_thirty_six_closed_are_eighteen_of_twenty_three_and_eight_by_the_metric :
    ∀ b ∈ the_arms, ∀ d ∈ the_arms,
      the_contraction_of the_source_on_the_arms b d
        = 18 * (23 * (if b = d then 1 else 0) + 8 * the_metric_on_the_arms b d) := by decide

theorem closed_the_source_is_five_fifty_eight_and_two_seventy :
    the_arms.map (fun arm => the_contraction_of the_source_on_the_arms arm arm) = [558, 270, 558, 558] := by decide

--| TAKEN ONCE.  A pair by a pair is the same when the pairs change places, so thirty-six are twenty-one taken once.  And
--| the three where no arm is shared are bound by one equation: around three is nothing.
def the_pairs_of_pairs_taken_once : List ((Direction × Direction) × (Direction × Direction)) :=
  (List.range 6).flatMap fun this => ((List.range 6).filter (this ≤ ·)).filterMap fun that =>
    match the_pairs_of_arms[this]?, the_pairs_of_arms[that]? with
    | some one, some other => some (one, other)
    | _, _ => none

def share_no_arm (pairs : (Direction × Direction) × (Direction × Direction)) : Bool :=
  pairs.1.1 != pairs.2.1 && pairs.1.1 != pairs.2.2 && pairs.1.2 != pairs.2.1 && pairs.1.2 != pairs.2.2

theorem twenty_one_taken_once_and_three_that_share_no_arm :
    the_pairs_of_pairs_taken_once.length = 21
      ∧ (the_pairs_of_pairs_taken_once.filter share_no_arm).length = 3
      ∧ the_pairs_of_pairs_taken_once.length - 1 = 20 := by decide

end Measurement
